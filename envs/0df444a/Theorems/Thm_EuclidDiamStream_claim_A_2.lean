-- Prove2me | Theorems.Thm_EuclidDiamStream_claim_A_2
-- name    : EuclidDiamStream.claim_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:56.702021+00:00
-- url     : https://prove2.me/theorems/7c3bfb1d-8121-4970-8623-6dafec6abdc6
-- title:
--   Claim A.2 — $T^{(y)}\notin\mathrm{span}\{T^{(u)}:u\in\mathcal B(x,\tau)\}$ with probability $\ge1-4\delta$
-- statement:
--   Let $(T,\mathrm{Dec})$ be an $(s,\lambda)$-linear sketch with failure probability at most $\delta$ on $\mathcal D$. Writing $T^{(u)}$ for the column of $T$ at the cube point $u$,
--   $$\Pr_{x,y\sim\{0,1\}^d}\big[T^{(y)}\notin\mathrm{span}\{T^{(u)}:u\in\mathcal B(x,\tau)\}\big]\ge1-4\delta.$$
--   Here $d$ is large enough in terms of $\delta$, the integers $P,Q$ are chosen from $\lambda$ and the instance, and $U$ is any positive integer with $2Q<PU$ and $(1-2Q/(PU))^{n-1}\ge0.99$.
--
--   The claim converts the kernel statement of Claim A.1 into the statement about column spans that Definition 3.2 asks for.
--
--   Differences from the source:
--   - reading: P, Q set by (7) through s; U = ω((n − 1)·O(sλ)^{2s+2}) → P, Q chosen before s, depending on λ and the instance only; every U with 2Q < PU and (1 − 2Q/(PU))^{n−1} ≥ 0.99; reason: Lemma 3.3 fixes P, U before s, and this works because the rows of T can be reduced to a basis of its row space (s ≤ N) with the same kernel and column relations; the two inequalities are what U = ω(·) provides
--   - reading: "for d a large enough constant" (p.18) → ∃ d₀ (after δ) with d₀ ≤ hardDim n c; reason: the page's own qualifier; it is used only for Pr[Ham(x,y) ≥ d/3] ≥ 1 − δ
--   - encoding: n, c, Δ unrestricted in the context of Appendix A → 2 ≤ n, 1 < c, 1 ≤ Δ; reason: n ≥ 2 is what makes d(n,c) exist; c > 1 is Lemma 3.9's and Theorem 2's range; Δ ≥ 1 is what makes {0,1}^d a subset of {0,…,Δ}^d
--   - reading: r = 2√τ = √d/(c√3) (Def. 3.1, p.7) → r = hardScale n c = √d/(c√3); reason: the two printed values agree only when 12c² divides d, and 2√τ = 0 at τ = 0 violates r > 0; Lemma 3.9, p.13, fixes √d/(c√3)
--   - encoding: D draws x, y, v_y, then v_z on B(x,τ), with positive integers P, U → one uniform draw on Cube d × Cube d × Bool × (Cube d → Fin (PU)), mapped by hardVec, with P, U : ℕ+; the ball draw determines v_y when y ∈ B(x,τ); reason: the same law, following the order of the page
--   - encoding: Dec(Tv) ≠ diam_{r,c,n}(v), with diam_{r,c,n}(v) ∈ {0,1,∗} → some (Dec (T v)) ≠ diamGap r c n v; reason: Dec outputs a bit, so ∗ counts as an error, as footnote 11 (p.20) treats it
--   - encoding: a probability over uniform x, y → a count of pairs, at least (1 − 4δ)·4^d of the 4^d; reason: the same quantity
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.19, Claim A.2; parameters (7), p.17

import Mathlib
import Definitions.Def_EuclidDiamStream_hardDist
import Definitions.Def_EuclidDiamStream_IsLinearSketch

namespace EuclidDiamStream

open Classical in
/-- Claim A.2 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.19: for an `(s,λ)`-linear sketch `(T, Dec)` with failure probability at most `δ` on
`D`, `Pr_{x,y}[T^{(y)} ∉ span{T^{(u)} : u ∈ B(x,τ)}] ≥ 1 − 4δ`, where `T^{(u)}` is the column of `T` at the
embedded cube point `u`, cast to the reals.

**Formalization Note.** The parameters (7), p.17, are read as: `P, Q` chosen from `λ` and the instance, before
`s`, and every sufficiently large `U` (`2Q < PU` and `(1 − 2Q/(PU))^{n−1} ≥ 0.99`), which is what `U = ω(…)` of
(7) provides. "For `d` a large enough constant" (p.18) is `d₀`. -/
theorem claim_A_2 (δ : ℝ) (hδ : 0 < δ) :
    ∃ d₀ : ℕ, ∀ (n : ℕ) (c : ℝ) (Δ : ℕ), 2 ≤ n → 1 < c → 1 ≤ Δ → d₀ ≤ hardDim n c →
      ∀ lam : ℕ, ∃ (P : ℕ+) (Q : ℕ), 1 ≤ Q ∧
        ∀ U : ℕ+, 2 * Q < (P : ℕ) * (U : ℕ) →
          (99 / 100 : ℝ) ≤ (1 - 2 * (Q : ℝ) / ((P : ℕ) * (U : ℕ) : ℝ)) ^ (n - 1) →
        ∀ (s : ℕ) (T : Matrix (Fin s) (Point (hardDim n c) Δ) ℤ) (Dec : (Fin s → ℤ) → Bool),
          IsLinearSketch T lam → hardError n c Δ P U T Dec ≤ ENNReal.ofReal δ →
          (1 - 4 * δ) * 4 ^ hardDim n c ≤
            (((Finset.univ : Finset (Cube (hardDim n c) × Cube (hardDim n c))).filter (fun p =>
                (fun i => (T i (embed Δ p.2) : ℝ)) ∉
                  Submodule.span ℝ ((fun (u : Cube (hardDim n c)) (i : Fin s) => (T i (embed Δ u) : ℝ)) ''
                    (↑(hamBall p.1 (hardTau n c)) : Set (Cube (hardDim n c)))))).card : ℝ) := by sorry

end EuclidDiamStream
