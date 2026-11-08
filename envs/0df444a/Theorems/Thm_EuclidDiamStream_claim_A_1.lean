-- Prove2me | Theorems.Thm_EuclidDiamStream_claim_A_1
-- name    : EuclidDiamStream.claim_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:44.209469+00:00
-- url     : https://prove2.me/theorems/aa7e78dd-b7d9-4cea-8fe3-183c0aa1d772
-- title:
--   Claim A.1 — for most pairs, $\ker T$ has no short vector placing multiplicity $P$ on $y$
-- statement:
--   Let $(T,\mathrm{Dec})$ be an $(s,\lambda)$-linear sketch with error at most $\delta$ on $\mathcal D$. For $x,y\in\{0,1\}^d$, let $Z_{x,y}(P)$ be the set of vectors $z\in\mathbb Z^N$ satisfying
--   1. $z_y=P$,
--   2. $\|z\|_\infty\le Q$,
--   3. $z_u=0$ for every $u\notin\mathcal B(x,\tau)\cup\{y\}$.
--
--   Then, for $d$ large enough in terms of $\delta$, and for positive integers $P,Q,U$ with $2Q<PU$ and $(1-2Q/(PU))^{n-1}\ge0.99$, at least a $(1-4\delta)$ fraction of pairs $(x,y)$ satisfy
--   $$\ker(T)\cap Z_{x,y}(P)=\emptyset\quad\text{and}\quad y\notin\mathcal B(x,\tau).$$
--
--   A short kernel vector would let the sketch confuse a ball with a ball plus $y$, and this claim bounds how often that can happen.
--
--   Differences from the source:
--   - generalization: P, Q, U set as in (7) → any P, U ≥ 1, Q ≥ 1 with 2Q < PU and (1 − 2Q/(PU))^{n−1} ≥ 0.99; reason: these are the two facts of (7) that the claim uses, and the values of (7) satisfy them
--   - reading: "for d a large enough constant" (p.18) → ∃ d₀ (after δ) with d₀ ≤ hardDim n c; reason: the page's own qualifier; it is used only for Pr[Ham(x,y) ≥ d/3] ≥ 1 − δ
--   - encoding: n, c, Δ unrestricted in the context of Appendix A → 2 ≤ n, 1 < c, 1 ≤ Δ; reason: n ≥ 2 is what makes d(n,c) exist; c > 1 is Lemma 3.9's and Theorem 2's range; Δ ≥ 1 is what makes {0,1}^d a subset of {0,…,Δ}^d
--   - reading: r = 2√τ = √d/(c√3) (Def. 3.1, p.7) → r = hardScale n c = √d/(c√3); reason: the two printed values agree only when 12c² divides d, and 2√τ = 0 at τ = 0 violates r > 0; Lemma 3.9, p.13, fixes √d/(c√3)
--   - encoding: D draws x, y, v_y, then v_z on B(x,τ), with positive integers P, U → one uniform draw on Cube d × Cube d × Bool × (Cube d → Fin (PU)), mapped by hardVec, with P, U : ℕ+; the ball draw determines v_y when y ∈ B(x,τ); reason: the same law, following the order of the page
--   - encoding: Dec(Tv) ≠ diam_{r,c,n}(v), with diam_{r,c,n}(v) ∈ {0,1,∗} → some (Dec (T v)) ≠ diamGap r c n v; reason: Dec outputs a bit, so ∗ counts as an error, as footnote 11 (p.20) treats it
--   - encoding: a probability over uniform x, y → a count of pairs, at least (1 − 4δ)·4^d of the 4^d; reason: the same quantity
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.18, Claim A.1; parameters (7), p.17

import Mathlib
import Definitions.Def_EuclidDiamStream_hardDist
import Definitions.Def_EuclidDiamStream_IsLinearSketch

namespace EuclidDiamStream

open Classical in
/-- Claim A.1 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.18. For `(T, Dec)` an `(s,λ)`-linear sketch with error at most `δ` on `D`, for at
least a `(1 − 4δ)` fraction of pairs `(x,y)`: no `z ∈ ℤ^N` with `z_y = P`, `‖z‖_∞ ≤ Q`, and `z_u = 0` for every
`u ∉ B(x,τ) ∪ {y}` lies in `ker T`, and `y ∉ B(x,τ)`.

**Formalization Note.** "For `d` a large enough constant" (p.18) is `d₀`, chosen after `δ`. Instead of (7), the
statement takes any `P, Q, U` with `2Q < PU` and `(1 − 2Q/(PU))^{n−1} ≥ 0.99`, the two facts the proof uses. -/
theorem claim_A_1 (δ : ℝ) (hδ : 0 < δ) :
    ∃ d₀ : ℕ, ∀ (n : ℕ) (c : ℝ) (Δ : ℕ), 2 ≤ n → 1 < c → 1 ≤ Δ → d₀ ≤ hardDim n c →
      ∀ (P U : ℕ+) (Q : ℕ), 1 ≤ Q → 2 * Q < (P : ℕ) * (U : ℕ) →
        (99 / 100 : ℝ) ≤ (1 - 2 * (Q : ℝ) / ((P : ℕ) * (U : ℕ) : ℝ)) ^ (n - 1) →
      ∀ (s lam : ℕ) (T : Matrix (Fin s) (Point (hardDim n c) Δ) ℤ) (Dec : (Fin s → ℤ) → Bool),
        IsLinearSketch T lam → hardError n c Δ P U T Dec ≤ ENNReal.ofReal δ →
        (1 - 4 * δ) * 4 ^ hardDim n c ≤
          (((Finset.univ : Finset (Cube (hardDim n c) × Cube (hardDim n c))).filter (fun p =>
              (∀ z : Point (hardDim n c) Δ → ℤ,
                z (embed Δ p.2) = ((P : ℕ) : ℤ) →
                (∀ u, |z u| ≤ (Q : ℤ)) →
                (∀ u, (∀ w ∈ hamBall p.1 (hardTau n c), u ≠ embed Δ w) → u ≠ embed Δ p.2 → z u = 0) →
                T.mulVec z ≠ 0) ∧
              hardTau n c < ham p.1 p.2)).card : ℝ) := by sorry

end EuclidDiamStream
