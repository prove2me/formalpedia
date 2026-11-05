-- Prove2me | Theorems.Thm_DotySW_Deranged_range_sigma_eq_centralizer
-- name    : DotySW.Deranged.range_sigma_eq_centralizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:36.600735+00:00
-- url     : https://prove2.me/theorems/1af3db82-fab1-4803-b1e0-18f56f67efd8
-- title:
--   Eq. (15) — $\sigma(\mathcal B^{(n)}_{r,s})=\mathrm{End}_{\mathrm{GL}_n}(V^{r,s})$
-- statement:
--   For all $n,r,s$, the operators on mixed tensor space $V^{r,s}$ that commute with the action of $\mathrm{GL}_n(\mathbb C)$ are exactly the images of the walled Brauer algebra:
--
--   $$
--   \sigma(\mathcal B^{(n)}_{r,s})=\mathrm{End}_{\mathrm{GL}_n}(V^{r,s}).
--   $$
--
--   This is one half of Schur-Weyl duality for mixed tensor space, and it carries the first fundamental theorem of invariant theory for $\mathrm{GL}_n$. There is no hypothesis $n\ge r+s$.
--
--   **Formalization Note** This is the form for the group with the left action, which the goal uses. The open platform theorem `WalledBrauer.SuperSchurWeyl.theorem_7_8`, taken with odd dimension $0$, is the form for the Lie algebra $\mathfrak{gl}_m$ with the right action. It is a reference item of this mission.
--
--   Differences from the source:
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → no positivity hypothesis on n; reason: n = 0 is the degenerate case V = 0, where the statement is still true, and no instance with n ≥ 1 changes
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, Eq. (15), p. 10

import Mathlib
import Definitions.Def_DotySW_Deranged_rho
import Definitions.Def_DotySW_Deranged_sigma

namespace DotySW.Deranged

/-- **Eq. (15): `σ(B^{(n)}_{r,s}) = End_{GL_n}(V^{r,s})`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, Eq. (15), p. 10.

The image of the walled Brauer algebra is exactly the commutant of `GL_n` on mixed tensor space.

**Formalization Note** Both inclusions, for all `n`, `r`, `s` (Eq. (15) has no hypothesis
`n ≥ r + s`). Stated for the group `GL_n(ℂ)` with the left action; the open platform theorem
`WalledBrauer.SuperSchurWeyl.theorem_7_8` at odd dimension `0` is the form for the Lie algebra
`gl_m` with the right action. -/
theorem range_sigma_eq_centralizer (n r s : ℕ) :
    Set.range (sigma n r s) =
      (Subalgebra.centralizer ℂ (Set.range (rho n r s)) : Set (Op n (r + s))) := by sorry

end DotySW.Deranged
