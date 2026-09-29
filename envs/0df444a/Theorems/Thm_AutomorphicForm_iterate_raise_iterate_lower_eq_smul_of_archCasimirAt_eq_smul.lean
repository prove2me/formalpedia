-- Prove2me | Theorems.Thm_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
-- name    : AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/2d7b8504-0dda-5cda-90e9-06a9b5b85c81
-- title:
--   Maass raising and lowering operators at a real place
-- statement:
--   Let $K$ be a number field and $w$ an infinite place of $K$ with $w$ real, and let $\theta$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathcal{O}_K$ in $K$ that is smooth at $w$, in the sense that for every $g$ the map sending a real $2\times 2$ matrix $e$ to $\theta(g\cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the set where $\det e \neq 0$. Write $D_H, D_E, D_{F^-}$ for the derivatives at $t=0$ of right translation by the one-parameter flows at $w$ in the three directions $H, E, F^-$, and let $\Omega = -\bigl(\tfrac14 D_HD_H - \tfrac12 D_H + D_ED_{F^-}\bigr)$. Assume $D_E\theta - D_{F^-}\theta = m\,\theta$ and $\Omega\theta = \lambda\,\theta$ for scalars $m,\lambda\in\mathbb{C}$. Set $E^{\mp} = D_H \mp i\,(D_E + D_{F^-})$ as operators on functions. Then for every $j\in\mathbb{N}$ the function $(E^-)^j\theta$ is smooth at $w$, satisfies $D_E - D_{F^-}$ eigenvalue $m - 2ij$ and $\Omega$-eigenvalue $\lambda$; likewise $(E^+)^j\theta$ with eigenvalue $m + 2ij$ and the same $\lambda$; and for every $M\in\mathbb{N}$, $(E^+)^M(E^-)^M\theta = \prod_{j<M}\bigl(-4\lambda + (m-2ij)^2 - 2i(m-2ij)\bigr)\theta$ and $(E^-)^M(E^+)^M\theta = \prod_{j<M}\bigl(-4\lambda + (m+2ij)^2 + 2i(m+2ij)\bigr)\theta$.
--
--   This is the function-level form of the $\mathfrak{sl}_2(\mathbb{R})$ Maass raising and lowering calculus at one real place: the weight shifts $[\mathfrak{k},E^{\mp}] = \mp 2i E^{\mp}$, the commuting of the Casimir with the flow derivatives, and the factorisation $E^{+}E^{-} = -4\Omega + \mathfrak{k}^2 - 2i\mathfrak{k}$ iterated $M$ times. It is used in the analysis of cuspidal constituents, where the explicit product is what forces non-vanishing of lowered vectors and pins down the archimedean Casimir eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAt hw θ) (m lam : ℂ)
    (hm : archDerivAt hw .E θ - archDerivAt hw .Fm θ = m • θ)
    (hΩ : archCasimirAt hw θ = lam • θ) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ, IsArchSmoothAt hw (lower^[j] θ) ∧
      archDerivAt hw .E (lower^[j] θ) - archDerivAt hw .Fm (lower^[j] θ) = (m - 2 * Complex.I * j) • lower^[j] θ ∧
      archCasimirAt hw (lower^[j] θ) = lam • lower^[j] θ) ∧
    (∀ j : ℕ, IsArchSmoothAt hw (raise^[j] θ) ∧
      archDerivAt hw .E (raise^[j] θ) - archDerivAt hw .Fm (raise^[j] θ) = (m + 2 * Complex.I * j) • raise^[j] θ ∧
      archCasimirAt hw (raise^[j] θ) = lam • raise^[j] θ) ∧
    (∀ M : ℕ, raise^[M] (lower^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m - 2 * Complex.I * j) ^ 2 - 2 * Complex.I * (m - 2 * Complex.I * j))) • θ) ∧
    (∀ M : ℕ, lower^[M] (raise^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m + 2 * Complex.I * j) ^ 2 + 2 * Complex.I * (m + 2 * Complex.I * j))) • θ) := by sorry
