-- Prove2me | Theorems.Thm_DotySW_Deranged_sigma_injective
-- name    : DotySW.Deranged.sigma_injective
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:41.763906+00:00
-- url     : https://prove2.me/theorems/4d8afaa6-391a-4df9-a124-bdc9f14bf2a9
-- title:
--   §3.4 — $\sigma$ is faithful for $n\ge r+s$
-- statement:
--   If $n\ge r+s$, then $\sigma:\mathcal B^{(n)}_{r,s}\to\mathrm{End}(V^{r,s})$ is injective. Together with Eq. (15) this gives the isomorphism
--
--   $$
--   \mathcal B^{(n)}_{r,s}\simeq\mathrm{End}_{\mathrm{GL}_n}(V^{r,s}).
--   $$
--
--   The goal uses this case through $n\ge 2r$ with $s=r$.
--
--   **Formalization Note** Injectivity is stated; the isomorphism is its combination with `range_sigma_eq_centralizer` and `sigma_mul`. The open platform theorem `WalledBrauer.SuperSchurWeyl.theorem_7_8` contains the corresponding clause for the right action of $\mathfrak{gl}_m$.
--
--   Differences from the source:
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → no positivity hypothesis on n; reason: n = 0 is the degenerate case V = 0, where the statement is still true, and no instance with n ≥ 1 changes
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, unnumbered, p. 10

import Mathlib
import Definitions.Def_DotySW_Deranged_sigma

namespace DotySW.Deranged

/-- **`σ` is faithful when `n ≥ r + s`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, unnumbered, p. 10.

**Formalization Note** With `range_sigma_eq_centralizer` and `sigma_mul` this is the printed
isomorphism `B^{(n)}_{r,s} ≃ End_{GL_n}(V^{r,s})`. -/
theorem sigma_injective (n r s : ℕ) (h : r + s ≤ n) : Function.Injective (sigma n r s) := by sorry

end DotySW.Deranged
