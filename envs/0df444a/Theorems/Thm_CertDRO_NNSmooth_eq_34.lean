-- Prove2me | Theorems.Thm_CertDRO_NNSmooth_eq_34
-- name    : CertDRO.NNSmooth.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:33:33.396209+00:00
-- url     : https://prove2.me/theorems/a27fb2b3-118a-46d8-9d22-c51ee2aedd0b
-- title:
--   (34) — telescoping representation of J_xF_l(θ; x) − J_xF_l(θ; x′)
-- statement:
--   Let every operation $\sigma_l$, $l=1,\dots,L$, of a network of depth $L$ be differentiable. Then for every $l=0,\dots,L$ and all inputs $x,x'$,
--   $$J_xF_l(\theta;x)-J_xF_l(\theta;x')=\sum_{j=1}^{l}\underbrace{\Big(\prod_{k=j+1}^{l}\nabla\sigma_k(\theta_k\cdot F_{k-1}(\theta;x'))\cdot\theta_k\Big)}_{(a)}\cdot\underbrace{\big(\nabla\sigma_j(\theta_j\cdot F_{j-1}(\theta;x))-\nabla\sigma_j(\theta_j\cdot F_{j-1}(\theta;x'))\big)}_{(b)}\cdot\underbrace{\theta_j\cdot J_xF_{j-1}(\theta;x)}_{(c)},$$
--   where products are taken in network order, the empty product ($j=l$) is the identity, and $F_0(\theta;x)=x$.
--
--   This is the telescoping identity for a difference of products of linear maps, applied to the Jacobians of Lemma 6; the proof of the second half of Proposition 5 bounds each of (a), (b), (c) separately.
--
--   **Formalization Note** The paper's display first writes the difference of products as a "product of differences"; that line is a misprint (a difference of products is not a product of differences) and is not formalized. Only the telescoped sum, which is what the proof uses, is stated. In Lean the summation index $j$ is 0-based (summand $j$ is the paper's $j+1$), and term (a) is the tail product of the definition file, from layer $j+1$ to layer $l$, at the input $x'$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 45, §B.8, (34)

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

namespace CertDRO.NNSmooth

open Network

/-- (34) (§B.8, p. 45), the telescoping identity: if every `σ_l` of a depth-`L` network is
differentiable, then for `l ≤ L` and inputs `x, x'`,
`J_x F_l(θ; x) − J_x F_l(θ; x') = ∑_{j=1}^{l} (a)_j · (b)_j · (c)_j` with
(a) the tail product `∏_{k=j+1}^{l} ∇σ_k(θ_k · F_{k-1}(θ; x')) · θ_k` (at `x'`),
(b) `∇σ_j(θ_j · F_{j-1}(θ; x)) − ∇σ_j(θ_j · F_{j-1}(θ; x'))`, and
(c) `θ_j · J_x F_{j-1}(θ; x)` (at `x`).
In 0-based indices the summand `j ∈ range l` is the paper's `j + 1`. -/
theorem eq_34 (N : Network) (L : ℕ) (hσ : ∀ l < L, Differentiable ℝ (N.σ l)) :
    ∀ l ≤ L, ∀ x x' : E (N.dO 0),
      fderiv ℝ (N.F l) x - fderiv ℝ (N.F l) x' =
        ∑ j ∈ Finset.range l, (N.tailJac x' (j + 1) l).comp
          ((fderiv ℝ (N.σ j) (N.θ j (N.F j x)) - fderiv ℝ (N.σ j) (N.θ j (N.F j x'))).comp
            ((N.θ j).comp (fderiv ℝ (N.F j) x))) := by sorry

end CertDRO.NNSmooth
