-- Prove2me | Theorems.Thm_EuclidDiamStream_lemma_3_3
-- name    : EuclidDiamStream.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:01.577229+00:00
-- url     : https://prove2.me/theorems/fdfc80f9-07aa-46fa-ade9-bc5786674608
-- title:
--   Lemma 3.3 — a good sketch yields a ball-subspace-evading function
-- statement:
--   For any $\lambda\in\mathbb N$ there is a setting of $P,U\ge1$ such that, if $(T,\mathrm{Dec})$ is an $(s,\lambda)$-linear sketch with
--   $$\Pr_{v\sim\mathcal D}\big[\mathrm{Dec}(Tv)\ne\mathrm{diam}_{r,c,n}(v)\big]\le\delta,$$
--   then the column map $u\mapsto T^{(u)}$ is a $(4\delta,\tau)$-ball-subspace-evading function $\{0,1\}^d\to\mathbb R^s$. Here $d$ is large enough in terms of $\delta$.
--
--   This is the step that removes the decoder and leaves a purely linear-algebraic object.
--
--   Differences from the source:
--   - reading: an (O(δ),τ)-ball-subspace-evading function can be constructed → the column map u ↦ T^{(u)} is (4δ,τ)-ball-subspace-evading; reason: the explicit function and constant the proof gives (Claim A.2, p.19); this is the stronger form
--   - reading: "for d a large enough constant" (p.18) → ∃ d₀ (after δ) with d₀ ≤ hardDim n c; reason: the page's own qualifier; it is used only for Pr[Ham(x,y) ≥ d/3] ≥ 1 − δ
--   - encoding: n, c, Δ unrestricted in the context of Appendix A → 2 ≤ n, 1 < c, 1 ≤ Δ; reason: n ≥ 2 is what makes d(n,c) exist; c > 1 is Lemma 3.9's and Theorem 2's range; Δ ≥ 1 is what makes {0,1}^d a subset of {0,…,Δ}^d
--   - reading: r = 2√τ = √d/(c√3) (Def. 3.1, p.7) → r = hardScale n c = √d/(c√3); reason: the two printed values agree only when 12c² divides d, and 2√τ = 0 at τ = 0 violates r > 0; Lemma 3.9, p.13, fixes √d/(c√3)
--   - encoding: D draws x, y, v_y, then v_z on B(x,τ), with positive integers P, U → one uniform draw on Cube d × Cube d × Bool × (Cube d → Fin (PU)), mapped by hardVec, with P, U : ℕ+; the ball draw determines v_y when y ∈ B(x,τ); reason: the same law, following the order of the page
--   - encoding: Dec(Tv) ≠ diam_{r,c,n}(v), with diam_{r,c,n}(v) ∈ {0,1,∗} → some (Dec (T v)) ≠ diamGap r c n v; reason: Dec outputs a bit, so ∗ counts as an error, as footnote 11 (p.20) treats it
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.8, Lemma 3.3 (restated p.17); proof pp.17–19

import Mathlib
import Definitions.Def_EuclidDiamStream_hardDist
import Definitions.Def_EuclidDiamStream_IsLinearSketch
import Definitions.Def_EuclidDiamStream_IsBallSubspaceEvading

namespace EuclidDiamStream

/-- Lemma 3.3 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.8 (restated p.17): for any `λ ∈ ℕ` there is a setting of `P, U ≥ 1` such that if
`(T, Dec)` is an `(s,λ)`-linear sketch with `Pr_{v∼D}[Dec(Tv) ≠ diam_{r,c,n}(v)] ≤ δ`, then one can construct
an `(O(δ),τ)`-ball-subspace-evading function `f : {0,1}^d → ℝ^s`.

**Formalization Note.** `O(δ)` is `4δ` and `f` is the column map `u ↦ T^{(u)}`, both from the proof (Claim A.2 and
p.19). `P, U` come before `s`, in the order printed. `d₀` is "for `d` a large enough constant" (p.18). -/
theorem lemma_3_3 (δ : ℝ) (hδ : 0 < δ) :
    ∃ d₀ : ℕ, ∀ (n : ℕ) (c : ℝ) (Δ : ℕ), 2 ≤ n → 1 < c → 1 ≤ Δ → d₀ ≤ hardDim n c →
      ∀ lam : ℕ, ∃ P U : ℕ+,
        ∀ (s : ℕ) (T : Matrix (Fin s) (Point (hardDim n c) Δ) ℤ) (Dec : (Fin s → ℤ) → Bool),
          IsLinearSketch T lam → hardError n c Δ P U T Dec ≤ ENNReal.ofReal δ →
          IsBallSubspaceEvading (4 * δ) (hardTau n c)
            (fun (u : Cube (hardDim n c)) (i : Fin s) => (T i (embed Δ u) : ℝ)) := by sorry

end EuclidDiamStream
