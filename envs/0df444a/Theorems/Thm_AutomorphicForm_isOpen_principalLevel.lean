-- Prove2me | Theorems.Thm_AutomorphicForm_isOpen_principalLevel
-- name    : AutomorphicForm.isOpen_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/415750e3-cfa5-5756-83be-abc026e041e9
-- title:
--   Openness of the principal level K(N) in GL₂(A_F)
-- statement:
--   Let $F$ be a number field and let $N$ be an ideal of its ring of integers $\mathcal{O}_F$ with $N \neq \bot$, i.e. $N$ non-zero. Write $\mathrm{AdelicGL2}$ for $\mathrm{GL}_2$ of the full adele ring of $F$, that is the general linear group of $2 \times 2$ matrices over $\mathrm{AdeleRing}\ \mathcal{O}_F\ F$, with its topology. The subgroup `principalLevel` attached to $N$ is by definition the intersection of `levelOne` for $N$ — the preimage under the map `glFin` (passage from the full adelic matrix group to the finite-adelic one) of the subgroup `finiteLevelOne` of $\mathrm{GL}_2$ of the finite adeles, so that the condition imposed by $N$ is a congruence condition at the finite places only and no condition is imposed at the archimedean places — with the image of that same subgroup under conjugation by the Weyl element $w = \begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$, viewed as an element of $\mathrm{GL}_2$ of the adeles (it is its own inverse). The theorem asserts that the underlying set of this subgroup is open in $\mathrm{GL}_2$ of the adeles of $F$.
--
--   This is the openness half of the classical statement that the principal congruence level $K(N)$ is a compact open subgroup of $\mathrm{GL}_2$ of the finite adeles, here in the shape needed for the full adelic group with no condition at the infinite places. It serves to discharge the openness hypothesis of the level-generic statements in the adelic theory of automorphic forms on $\mathrm{GL}_2$, and is cited by the results on cuspidal spectra, orthonormal families and induced sections at principal congruence level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOpen_principalLevel.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isOpen_principalLevel
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    IsOpen ((principalLevel (𝓞 F) F N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by sorry
