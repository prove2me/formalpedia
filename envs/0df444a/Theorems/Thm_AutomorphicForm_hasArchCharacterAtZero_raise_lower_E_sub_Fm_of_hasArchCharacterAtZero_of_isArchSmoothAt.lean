-- Prove2me | Theorems.Thm_AutomorphicForm_hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt
-- name    : AutomorphicForm.hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/54c1165a-e971-585d-9746-a4b5f4b46fec
-- title:
--   Raising and lowering operators shift the archimedean weight by 2
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with $hw$ a witness that $w$ is real, $n$ an integer, and $\psi \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ a complex-valued function on the adelic group $\mathrm{GL}_2$ of $K$. Assume $\psi$ is smooth at $w$ in the sense of `IsArchSmoothAt hw`: for every adelic $g$, the function $e \mapsto \psi(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$ on $2 \times 2$ real matrices is $C^\infty$ on the open set where $\det e \neq 0$, the lift sending an invertible $e$ to the element of $\mathrm{GL}_2(\mathbb{A}_K)$ obtained from $e$ at the real place $w$. Assume further that $\psi$ satisfies the predicate `HasArchCharacterAt₀ K w (archWeightCharAt hw n)`, i.e. it has, at $w$, the character $\mathrm{archWeightCharAt}\,hw\,n$, the $n$-th power of the basic weight character $\mathrm{archWeightOneAt}\,hw$ of $\mathrm{rowIsometrySubgroup₀}$ of the completion $K_w$, transported along the identification of $K_w$ with $\mathbb{R}$ furnished by $hw$. For $d \in \{H, E, F^-\}$ write $\mathrm{archDerivAt}\,hw\,d\,\psi$ for the function $g \mapsto \frac{d}{dt}\psi\big(g \cdot \mathrm{archRealGLAt}\,hw\,(\mathrm{archFlowMatrix}\,d\,t)\big)\big|_{t=0}$. Then three conclusions hold simultaneously: $H\psi + i(E\psi + F^-\psi)$ has the character $\mathrm{archWeightCharAt}\,hw\,(n+2)$ at $w$; $H\psi - i(E\psi + F^-\psi)$ has the character $\mathrm{archWeightCharAt}\,hw\,(n-2)$; and $E\psi - F^-\psi$ has the character $\mathrm{archWeightCharAt}\,hw\,n$.
--
--   This is the standard behaviour of the raising and lowering operators $R = H + i(E+F)$ and $L = H - i(E+F)$ and of the compact generator $Z = E - F$ of $\mathfrak{sl}_2(\mathbb{R})$ acting on a function of pure $\mathrm{SO}(2)$-weight $n$ at a real place, in the adelic setting used here. It feeds the uniform $L^p$ estimates for iterated $E-F$ derivatives in [`AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule`](thm.html#AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (hψ : IsArchSmoothAt hw ψ)
    (hwt : HasArchCharacterAt₀ K w (archWeightCharAt hw n) ψ) :
    HasArchCharacterAt₀ K w (archWeightCharAt hw (n + 2))
        (archDerivAt hw .H ψ + Complex.I • (archDerivAt hw .E ψ + archDerivAt hw .Fm ψ)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n - 2))
        (archDerivAt hw .H ψ - Complex.I • (archDerivAt hw .E ψ + archDerivAt hw .Fm ψ)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw n) (archDerivAt hw .E ψ - archDerivAt hw .Fm ψ) := by sorry
