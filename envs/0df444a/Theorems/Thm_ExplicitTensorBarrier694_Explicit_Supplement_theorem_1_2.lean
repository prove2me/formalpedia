-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_Supplement_theorem_1_2
-- name    : ExplicitTensorBarrier694.Explicit.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:40:55.235951+00:00
-- url     : https://prove2.me/theorems/591b2f2b-28ab-419d-bc3c-b6749252a377
-- title:
--   Theorem 1.2 — optimal potency of linear flattenings: $2n-2\le\Pi(n)\le2n-2+\frac{2}{n+1}$
-- statement:
--   For a nonzero linear map $L:(\mathbb C^n)^{\otimes3}\to\mathrm{Mat}_{u,v}(\mathbb C)$ let $\rho(L)=\max_{x,y,z}\operatorname{rank}L(x\otimes y\otimes z)$ and $\mathrm{Pot}(L)=\max_T\operatorname{rank}L(T)/\rho(L)$, and let $\Pi(n)$ be the supremum of $\mathrm{Pot}(L)$ over all nonzero linear flattenings and all positive $u,v$. For every $n\ge2$,
--
--   $$2n-2\le\Pi(n)\le2n-2+\frac{2}{n+1}.$$
--
--   For odd $n=2p+1$ the upper bound holds with equality, $\Pi(n)=2n-2+\frac{2}{n+1}$, and it is attained by the central Koszul flattening $K_p$, $p=(n-1)/2$, of Definition 2.2:
--
--   $$\mathrm{Pot}(K_p)=2n-2+\frac{2}{n+1}.$$
--
--   The theorem shows that linear flattenings cannot certify border rank above roughly $2n$, and determines the optimal potency exactly in odd dimensions. It is a companion result to the mission goal and is not used in its proof. This is a paper-proved result awaiting a formal proof (the even-$n$ lower bound is proved in the cited work of Landsberg).
--
--   Differences from the source:
--   - encoding: (ℂⁿ)^{⊗3} and pure tensors x ⊗ y ⊗ z → coordinate arrays Tensor n n n = Fin n → Fin n → Fin n → ℂ (published), pure x y z with entries x_i y_j z_k; reason: the standard basis identifies the two spaces; ranks and linear maps are transported unchanged
--   - encoding: Π(n) a supremum of real numbers → an EReal supremum (optimalPotency n); reason: avoids the junk value of a real sSup of an unbounded set; the upper bound therefore also asserts that the potencies are bounded
--   - encoding: Pot of the central Koszul flattening, a matrix between Λ^p A ⊗ B* and Λ^{p+1} A ⊗ C → potency of T ↦ koszul p T, with ρ and Pot defined for matrices over arbitrary finite index types; reason: the same ρ and Pot as in Π(n); ranks are unchanged by reindexing rows and columns, so this is the source's potency of K_p
--   - encoding: for odd n, the central Koszul flattening K_{(n−1)/2} → for every p with n = 2p+1, koszul p; reason: the same instances
--   - encoding: u, v positive integers → u v : ℕ, with L ≠ 0; reason: a nonzero linear map into Mat_{u,v} forces u, v ≥ 1, so u = 0 or v = 0 adds no instance
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Theorem 1.2, p.2, equation (1.3); definitions (1.2) p.2; proofs §4 p.15 and §5 p.15 (PDF same); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Supplement_Flattening
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Koszul

namespace ExplicitTensorBarrier694.Explicit.Supplement

open ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Theorem 1.2, p.2, equation (1.3).
For every n ≥ 2: 2n − 2 ≤ Π(n) ≤ 2n − 2 + 2/(n+1). For odd n = 2p+1 the upper bound is an
equality, and it is attained by the central Koszul flattening K_p, p = (n−1)/2, whose
potency (same ρ and Pot as in Π(n)) equals 2n − 2 + 2/(n+1). Π(n) is an `EReal`
supremum, so the upper bound is not vacuous. -/
theorem theorem_1_2 (n : ℕ) (hn : 2 ≤ n) :
    (((2 * (n : ℝ) - 2 : ℝ)) : EReal) ≤ optimalPotency n ∧
    optimalPotency n ≤ (((2 * (n : ℝ) - 2 + 2 / ((n : ℝ) + 1) : ℝ)) : EReal) ∧
    ∀ p : ℕ, n = 2 * p + 1 →
      optimalPotency n = (((2 * (n : ℝ) - 2 + 2 / ((n : ℝ) + 1) : ℝ)) : EReal) ∧
      potency (fun T : Tensor n n n => koszul p T) =
        2 * (n : ℝ) - 2 + 2 / ((n : ℝ) + 1) := by sorry

end ExplicitTensorBarrier694.Explicit.Supplement
