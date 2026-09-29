-- Prove2me | Theorems.Thm_AutomorphicForm_isArchLoweringAnnihilatedAt_iff_isArchSmoothAt_and_lower_eq_zero_of_hasArchCharacterAt
-- name    : AutomorphicForm.isArchLoweringAnnihilatedAt_iff_isArchSmoothAt_and_lower_eq_zero_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/902d76d1-1992-5fcd-8488-2acbc0a56cba
-- title:
--   Lowering annihilation at a real place: slices versus flow derivatives
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with $w$ real (witnessed by `hw`), $k$ an integer, and $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ a continuous function on the adelic group `AdelicGL2 (𝓞 F) F`. Assume: (i) `hk`, that $\varphi$ satisfies `HasArchCharacterAt₀` at $w$ for the character obtained by composing the weight-$k$ character `archWeightCharℝ k` with the transport `rowIsometrySubgroup₀Map` along the identification `ringEquivRealOfIsReal hw` of the completion at $w$ with $\mathbb{R}$ (a norm-preserving identification, as recorded by `norm_ringEquivRealOfIsReal hw`); (ii) a homomorphism $\xi$ from the full unit group of the adele ring (as the top subgroup) to $\mathbb{C}^\times$ with $\varphi(\mathrm{diag}(z,z)\,g)=\xi(z)\varphi(g)$ for all $z$ and all $g$, where the central scalar is `centralScalar (𝓞 F) F`; (iii) a complex number $c_0$ such that for every real unit $t$ with $t>0$ and every $g$, $\varphi$ of the scalar matrix $t$ at $w$ (embedded by `adelicArchGLInclAt F w` after transport along `ringEquivRealOfIsReal hw`) times $g$ equals $t^{c_0}\varphi(g)$. The conclusion is an equivalence. On the left, `IsArchLoweringAnnihilatedAt w hw φ`: for every $g$ and every $z$ in the upper half-plane, the slice $m\mapsto \varphi\bigl(g\cdot \iota_w(m)\bigr)$ (extended by $0$ where $\det m=0$) is real-differentiable at $\begin{pmatrix}\operatorname{Im}z&\operatorname{Re}z\\0&1\end{pmatrix}$ and the operator $f\mapsto \tfrac12\bigl(Df(m)[m\,\mathrm{diag}(1,-1)]-i\,Df(m)[m\,\binom{0\ 1}{1\ 0}]\bigr)$ vanishes on it there. On the right, the conjunction of `IsArchSmoothAt hw φ` — for every $g$, the map $e\mapsto\varphi(g\cdot\text{archRealLiftAt } hw\ e)$ is $C^\infty$ on $\{\det e\neq 0\}$ — and the identity $\mathrm{D}_H\varphi-i\,(\mathrm{D}_E\varphi+\mathrm{D}_{F^-}\varphi)=0$ of functions, where $\mathrm{D}_d\varphi(g)$ is the derivative at $t=0$ of $t\mapsto\varphi(g\cdot\text{archFlowAt } hw\ d\ t)$ for the three directions $H$, $E$, $F^-$.
--
--   This is a dictionary between two ways of expressing that an automorphic form of weight $k$ at a real place is annihilated by the lowering operator $L=\tfrac12(H-i(E+F))$: as a Fréchet-derivative condition on Iwasawa slices over the upper half-plane, and as a flow-derivative identity in the Lie-algebra vocabulary used for the Casimir computations. It is invoked in the analysis of which archimedean weights occur in a lowering-annihilated form, including the occurrence and positivity statements used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchLoweringAnnihilatedAt_iff_isArchSmoothAt_and_lower_eq_zero_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.isArchLoweringAnnihilatedAt_iff_isArchSmoothAt_and_lower_eq_zero_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g)
    (c₀ : ℂ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) :
    IsArchLoweringAnnihilatedAt w hw φ ↔
      (IsArchSmoothAt hw φ ∧
        archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) := by sorry
