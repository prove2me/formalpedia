-- Prove2me | Theorems.Thm_CertDRO_NNSmooth_lemma_6
-- name    : CertDRO.NNSmooth.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:32:52.216025+00:00
-- url     : https://prove2.me/theorems/0640f752-a333-498c-b1ed-32be9e4a5ff5
-- title:
--   Lemma 6 — chain rule for the Jacobian of a layered network
-- statement:
--   Let $F_l(\theta;x)$ be the output of the first $l$ layers of a network of depth $L$, as in (20), and suppose every operation $\sigma_l$, $l=1,\dots,L$, is differentiable. Then:
--
--   1. for every $l=0,\dots,L$ the map $x\mapsto F_l(\theta;x)$ is differentiable;
--   2. for every $l=1,\dots,L$ its Jacobian satisfies the recursion
--   $$J_xF_l(\theta;x)=\nabla\sigma_l\big(\theta_l\cdot F_{l-1}(\theta;x)\big)\cdot\theta_l\cdot J_xF_{l-1}(\theta;x);$$
--   3. for every $l=0,\dots,L$, unrolling the recursion,
--   $$J_xF_l(\theta;x)=\prod_{k=1}^{l}\nabla\sigma_k\big(\theta_k\cdot F_{k-1}(\theta;x)\big)\cdot\theta_k,$$
--   the product taken in network order $A_l\cdots A_1$ (the identity for $l=0$).
--
--   Here $\nabla\sigma_k$ denotes the Jacobian of $\sigma_k$. The recursion is the basis of the smoothness bounds of Proposition 5 and of the telescoping representation (34).
--
--   **Formalization Note** Layers are 0-based in Lean (Lean layer `l` is the paper's $l+1$). Part 2 is a `HasFDerivAt` statement for $F_{l+1}$ with the composed derivative; part 3 identifies `fderiv (F l) x` with the tail product of the definition file taken from layer $0$ at the same input $x$. The paper prints the product with upper index $L$; it is read as $l$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 44, §B.8, Lemma 6

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

namespace CertDRO.NNSmooth

open Network

/-- Lemma 6 (§B.8, p. 44). If `σ_l` is differentiable for every layer of a depth-`L` network, then
every `x ↦ F_l(θ; x)`, `l ≤ L`, is differentiable; its Jacobian satisfies the chain-rule recursion
`J_x F_{l+1}(θ; x) = Jσ_{l+1}(θ_{l+1} · F_l(θ; x)) · θ_{l+1} · J_x F_l(θ; x)` (0-based: layer `l`);
and it equals the product `∏ ∇σ_k(θ_k · F_{k-1}(θ; x)) · θ_k` over all `l` layers, i.e. the tail
product `tailJac x 0 l` taken at the same input `x`. -/
theorem lemma_6 (N : Network) (L : ℕ) (hσ : ∀ l < L, Differentiable ℝ (N.σ l)) :
    (∀ l ≤ L, Differentiable ℝ (N.F l)) ∧
    (∀ l < L, ∀ x : E (N.dO 0),
      HasFDerivAt (N.F (l + 1))
        ((fderiv ℝ (N.σ l) (N.θ l (N.F l x))).comp ((N.θ l).comp (fderiv ℝ (N.F l) x))) x) ∧
    (∀ l ≤ L, ∀ x : E (N.dO 0), fderiv ℝ (N.F l) x = N.tailJac x 0 l) := by sorry

end CertDRO.NNSmooth
