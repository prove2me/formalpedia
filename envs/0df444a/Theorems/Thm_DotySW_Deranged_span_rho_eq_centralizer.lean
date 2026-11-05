-- Prove2me | Theorems.Thm_DotySW_Deranged_span_rho_eq_centralizer
-- name    : DotySW.Deranged.span_rho_eq_centralizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:38.320033+00:00
-- url     : https://prove2.me/theorems/249c8fda-42da-4e42-832a-8499e083347c
-- title:
--   Eq. (14) — $\rho(\mathbb C\mathrm{GL}_n)=\mathrm{End}_{\mathcal B^{(n)}_{r,s}}(V^{r,s})$
-- statement:
--   For all $n,r,s$, the operators on $V^{r,s}$ that commute with the action of the walled Brauer algebra are exactly the linear combinations of the operators $\rho(g)$, $g\in\mathrm{GL}_n(\mathbb C)$:
--
--   $$
--   \rho(\mathbb C\mathrm{GL}_n)=\mathrm{End}_{\mathcal B^{(n)}_{r,s}}(V^{r,s}).
--   $$
--
--   This is the second half of Schur-Weyl duality for mixed tensor space. The algebra on the right is the rational Schur algebra $S(n;r,s)$ of p. 10.
--
--   Differences from the source:
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
--   - encoding: $\rho(\mathbb C\mathrm{GL}_n)$ → the linear span of the operators ρ(g); reason: the image of the group algebra is by definition this span
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → no positivity hypothesis on n; reason: n = 0 is the degenerate case V = 0, where the statement is still true, and no instance with n ≥ 1 changes
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, Eq. (14), p. 10

import Mathlib
import Definitions.Def_DotySW_Deranged_rho
import Definitions.Def_DotySW_Deranged_sigma

namespace DotySW.Deranged

/-- **Eq. (14): `ρ(ℂGL_n) = End_{B^{(n)}_{r,s}}(V^{r,s})`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, Eq. (14), p. 10.

The linear span of `GL_n` on mixed tensor space is exactly the commutant of the walled Brauer
algebra.

**Formalization Note** The image `ρ(ℂGL_n)` of the group algebra is the linear span of the
operators `ρ(g)`. Both inclusions, for all `n`, `r`, `s`. -/
theorem span_rho_eq_centralizer (n r s : ℕ) :
    Submodule.span ℂ (Set.range (rho n r s)) =
      Subalgebra.toSubmodule (Subalgebra.centralizer ℂ (Set.range (sigma n r s))) := by sorry

end DotySW.Deranged
