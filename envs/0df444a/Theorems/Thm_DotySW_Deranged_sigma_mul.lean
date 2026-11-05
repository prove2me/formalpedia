-- Prove2me | Theorems.Thm_DotySW_Deranged_sigma_mul
-- name    : DotySW.Deranged.sigma_mul
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:38.725161+00:00
-- url     : https://prove2.me/theorems/67d06b80-9db8-422e-9013-17c86ddf2ff1
-- title:
--   §3.4 — $\sigma$ is a representation of $\mathcal B^{(n)}_{r,s}$ on $V^{r,s}$
-- statement:
--   For all $n,r,s$, the linear map $\sigma:\mathcal B^{(n)}_{r,s}\to\mathrm{End}(V^{r,s})$ is a unital algebra homomorphism:
--
--   $$
--   \sigma(xy)=\sigma(x)\sigma(y),\qquad \sigma(1)=1,
--   $$
--
--   and on diagrams
--
--   $$
--   \sigma(D_1)\,\sigma(D_2)=n^{\delta(D_1,D_2)}\,\sigma(D_1\circ D_2),
--   $$
--
--   where $\delta(D_1,D_2)$ is the number of interior loops formed when $D_1$ is stacked over $D_2$.
--
--   This says that the action of walled diagrams on mixed tensor space obtained by restricting the Brauer action is an action of the algebra, which is what the arrow $\sigma$ of the diagram (13) means.
--
--   Differences from the source:
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → no positivity hypothesis on n; reason: n = 0 is the degenerate case V = 0, where the statement is still true, and no instance with n ≥ 1 changes
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, unnumbered and Eq. (13), p. 9

import Mathlib
import Definitions.Def_DotySW_Deranged_sigma

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **`σ` is a representation of `B^{(n)}_{r,s}` on `V^{r,s}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, unnumbered and Eq. (13), p. 9.

`σ` is multiplicative and unital, and on diagrams this is the rule
`σ(D₁) σ(D₂) = n^{δ(D₁,D₂)} σ(D₁ ∘ D₂)`.

**Formalization Note** No hypothesis on `n`, `r`, `s`. Conventions as in `diagOp`: top row = output,
`D₁` stacked over `D₂`. -/
theorem sigma_mul (n r s : ℕ) :
    (∀ x y : WB n r s, sigma n r s (x * y) = sigma n r s x * sigma n r s y) ∧
    sigma n r s 1 = 1 ∧
    ∀ D₁ D₂ : WalledDiagram r s,
      diagOp n D₁ * diagOp n D₂ =
        (n : ℂ) ^ loops D₁.1 D₂.1 • diagOp n (WalledDiagram.comp D₁ D₂) := by sorry

end DotySW.Deranged
