-- Prove2me | Theorems.Thm_EuclidDiamStream_lemma_3_9
-- name    : EuclidDiamStream.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:34.754264+00:00
-- url     : https://prove2.me/theorems/a52542de-2340-45f4-8514-b03645c0f69b
-- title:
--   Lemma 3.9 (corrected: + $\Pr_{\mathcal D}[*]$ in (6)) — streaming-to-sketching reduction
-- statement:
--   There are absolute constants $K_1,K_2>0$ such that the following holds. Let $c>1$, $n\ge2$, let $d=d(n,c)$ and $r=\sqrt d/(c\sqrt3)$, and let $N=(\Delta+1)^d$. If $\mathcal A$ is a randomized streaming algorithm with bounded randomness complexity solving the $(r,c,n)$-diameter problem with error $\delta$, then for any $m\ge1$ there is an $(s,\lambda)$-linear sketch $(T,\mathrm{Dec})$ with $\lambda\le K_1(m^2N)^{N/2}$ and $s\log_2(m+1)\le\mathcal S^+(\mathcal A,m)$, satisfying
--   $$\Pr_{v\sim\mathcal D}\big[\mathrm{Dec}(Tv)\ne\mathrm{diam}_{r,c,n}(v)\big]\le K_2\delta+\Pr_{v\sim\mathcal D}\big[\mathrm{diam}_{r,c,n}(v)=*\big].$$
--
--   This is Theorem 4 of Khanna, Padaki, Singal, Waingarten (FOCS 2025) applied to $\mathcal D$, and it is the only step of the argument that this paper cites rather than proves.
--
--   **Formalization Note** The second term is the correction described in footnote 11, p.20. It tends to $0$ as $n\to\infty$, so the proof of the goal is unaffected.
--
--   Differences from the source:
--   - correction: (6): Pr_D[Dec(Tv) ≠ diam_{r,c,n}(v)] ≤ O(δ) → error ≤ K₂δ + Pr_D[diam_{r,c,n}(v) = ∗]; reason: the printed bound is false: the exact deterministic algorithm solves the problem for every δ > 0, and for c = 1.01, d(n,c) ≥ 200, there is an integer h ∈ (d/(3c²) − τ, d/3 − τ); with positive probability p∗ the draw has Ham(x,y) = h and v_y = P, so diam(v) = √(h+τ) ∈ (r, cr), value ∗, and every sketch errs, so the error is ≥ p∗ > O(δ) for small δ. Footnote 11 (p.20) gives this fix
--   - reading: O((m²N)^{N/2}) and O(δ) → K₁(m²N)^{N/2} and K₂δ with K₁, K₂ absolute, before δ; reason: δ is a fixed constant in the paper, so a constant allowed to depend on it would say nothing
--   - reading: "for any m ∈ ℕ", s ≤ S⁺(A,m)/log(m+1) → m ≥ 1 and s·log₂(m+1) ≤ S⁺(A,m) in ℝ≥0∞; reason: the source divides by log(m+1), and at m = 0 the entry bound forces T = 0; the base is 2 because S⁺ counts bits
--   - encoding: n ∈ ℕ, Δ arbitrary; an (s, O(·))-linear sketch → 2 ≤ n, 1 ≤ Δ; a natural λ with IsLinearSketch T λ and λ ≤ K₁(m²N)^{N/2}; reason: n ≥ 2 makes d(n,c) exist and Δ ≥ 1 makes D a distribution on the cube; T is integer, so a natural λ loses nothing
--   - reading: "any stream" in Def. 2.1 and Def. 2.3 → every strict-turnstile stream (BoolCSPDel.IsLegal), of any length and frequency; reason: footnote 6, p.6: the lower bounds work in the strict turnstile model
--   - reading: diam(v) a maximum over supp(v), which is empty at v = 0 → diam 0 = 0, so A must answer 0 on streams ending empty; reason: the usual diameter of the empty set; D never draws v = 0
--   - encoding: bounded randomness complexity; "all settings of randomness" → a Fintype seed type with any PMF, fixed before the stream; W⁺ over seeds in μ.support; reason: pp.3, 13: a finite amount of randomness independent of stream length; a seed of probability zero is never drawn
--   - encoding: S⁺(A,·) : ℕ → ℕ → spaceComplexity in ℕ∞, with ⊤ when W⁺ is infinite; reason: the state type is arbitrary; on a finite W⁺ it equals ⌈log₂|W⁺|⌉, and the bound holds trivially at ⊤
--   - encoding: D draws x, y, v_y, then v_z on B(x,τ), with positive integers P, U → one uniform draw on Cube d × Cube d × Bool × (Cube d → Fin (PU)), mapped by hardVec, with P, U : ℕ+; the ball draw determines v_y when y ∈ B(x,τ); reason: the same law, following the order of the page
--   - encoding: Dec(Tv) ≠ diam_{r,c,n}(v), with diam_{r,c,n}(v) ∈ {0,1,∗} → some (Dec (T v)) ≠ diamGap r c n v; reason: Dec outputs a bit, so ∗ counts as an error, as footnote 11 (p.20) treats it
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.13, Lemma 3.9; footnote 11, p.20; Appendix B, pp.19–20

import Mathlib
import Definitions.Def_EuclidDiamStream_hardDist
import Definitions.Def_EuclidDiamStream_IsLinearSketch
import Definitions.Def_EuclidDiamStream_Solves
import Definitions.Def_EuclidDiamStream_spaceComplexity

namespace EuclidDiamStream

/-- Lemma 3.9 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.13 (Theorem 4 of [KPSW25] applied with `D` from Definition 3.1), with its error bound
corrected as in footnote 11, p.20. For `n ∈ ℕ`, `c > 1`, `d` as in Definition 3.1 and `r = √d/(c√3)`: if `A` solves
`(r,c,n)`-diameter with bounded randomness complexity, then for any `m` there is an `(s, O((m²N)^{N/2}))`-linear
sketch `(T, Dec)` with `s ≤ S⁺(A,m)/log(m+1)` and `Pr_{v∼D}[Dec(Tv) ≠ diam_{r,c,n}(v)] ≤ O(δ) + Pr_{v∼D}[diam_{r,c,n}(v) = ∗]`.

**Formalization Note.** (6) as printed, with `O(δ)` alone, is false: every sketch errs on `∗` vectors, which have
fixed positive probability for some `c, n`, whereas `A` can be the exact algorithm for every `δ > 0`. Footnote 11
states the fix, applying [KPSW25] Theorem 4 to `D` conditioned on `{0,1}`. The `O`-constants `K₁, K₂` are absolute
and precede `δ`. `m` starts at `1`: the source divides by `log(m+1)`, and `s ≤ S⁺/log₂(m+1)` is written
multiplicatively in `ℝ≥0∞`. -/
theorem lemma_3_9 :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ δ : ℝ, 0 < δ → ∀ c : ℝ, 1 < c → ∀ n : ℕ, 2 ≤ n →
      ∀ Δ : ℕ, 1 ≤ Δ → ∀ P U : ℕ+,
      ∀ (R W : Type) [Fintype R] (A : StreamAlg (Point (hardDim n c) Δ) R W),
        A.Solves (hardScale n c) c n δ →
        ∀ m : ℕ, 1 ≤ m →
          ∃ (s lam : ℕ) (T : Matrix (Fin s) (Point (hardDim n c) Δ) ℤ) (Dec : (Fin s → ℤ) → Bool),
            IsLinearSketch T lam ∧
            (lam : ℝ) ≤ K₁ * (((m : ℝ) ^ 2 * (Fintype.card (Point (hardDim n c) Δ) : ℝ)) ^
              ((Fintype.card (Point (hardDim n c) Δ) : ℝ) / 2)) ∧
            (s : ENNReal) * ENNReal.ofReal (Real.logb 2 ((m : ℝ) + 1)) ≤
              ((A.spaceComplexity m : ℕ∞) : ENNReal) ∧
            hardError n c Δ P U T Dec ≤
              ENNReal.ofReal (K₂ * δ) +
                (hardDist n c Δ P U).toOuterMeasure {v | diamGap (hardScale n c) c n v = none} := by sorry

end EuclidDiamStream
