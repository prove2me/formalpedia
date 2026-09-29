-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm
-- name    : AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/16b70490-c5b4-5890-a089-873010bd19df
-- title:
--   Flow derivatives at a complex place: smoothness, linearity, brackets
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ and $hw$ a witness that $w$ is complex. Functions are $\mathbb{C}$-valued functions on $\mathrm{GL}_2$ of the adele ring of $F$ (that is, `AdelicGL2 (𝓞 F) F`), and for each of the six constructors $d$ of the finite type `ArchDirComplex`, namely `.H`, `.E`, `.Fm`, `.iH`, `.iE`, `.iFm`, the operator `archDerivAtComplex hw d` sends $\varphi$ to $g \mapsto \frac{d}{dt}\varphi\big(g\cdot \text{archFlowAtComplex } hw\, d\, t\big)\big|_{t=0}$, the derivative at $t=0$ along the one-parameter family of adelic matrices obtained by placing the matrices `archFlowMatrixComplex d t` at the place $w$; and $\varphi$ satisfies `IsArchSmoothAtComplex hw` when for every $g$ the map $e \mapsto \varphi(g\cdot \text{archComplexLiftAt } hw\, e)$, on $2\times 2$ complex matrices $e$, is real-$C^\infty$ on the open set where $\det e \neq 0$. The theorem asserts four things simultaneously: (i) for every such smooth $\varphi$ and every $d$, `archDerivAtComplex hw d φ` is again smooth in this sense; (ii) for smooth $\varphi,\psi$ and every $d$, the operator is additive, $D_d(\varphi+\psi)=D_d\varphi+D_d\psi$; (iii) for every $c\in\mathbb{C}$, every $\varphi$ (no smoothness assumed) and every $d$, $D_d(c\cdot\varphi)=c\cdot D_d\varphi$; and (iv) for every smooth $\varphi$, the fifteen commutator identities $D_XD_Y\varphi-D_YD_X\varphi=D_{[X,Y]}\varphi$ over the unordered pairs from the six directions, written out as $[H,E]=2E$, $[H,F]=-2F$, $[E,F]=H$, $[H,iH]=0$, $[H,iE]=2iE$, $[H,iF]=-2iF$, $[E,iH]=-2iE$, $[E,iE]=0$, $[E,iF]=iH$, $[F,iH]=2iF$, $[F,iE]=-iH$, $[F,iF]=0$, $[iH,iE]=-2E$, $[iH,iF]=2F$, $[iE,iF]=-H$.
--
--   This is the statement that right differentiation along the six real one-parameter subgroups at a complex place defines an action of $\mathfrak{sl}_2(\mathbb{C})$, regarded as a six-dimensional real Lie algebra, on the functions smooth at that place. It is the analytic input for the complex-place Casimir calculus: it is used by the identities comparing the two Casimir operators at a complex place with iterated flow derivatives, by their compatibility with the real-place Casimir operator, and by the $L^p$ bounds for iterated derivatives of Casimir eigenfunctions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex) :
    (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsArchSmoothAtComplex hw φ →
      ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ)) ∧
    (∀ φ ψ : AdelicGL2 (𝓞 F) F → ℂ, IsArchSmoothAtComplex hw φ → IsArchSmoothAtComplex hw ψ →
      ∀ d : ArchDirComplex,
        archDerivAtComplex hw d (φ + ψ) = archDerivAtComplex hw d φ + archDerivAtComplex hw d ψ) ∧
    (∀ (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (d : ArchDirComplex),
      archDerivAtComplex hw d (c • φ) = c • archDerivAtComplex hw d φ) ∧
    (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsArchSmoothAtComplex hw φ →
      (archDerivAtComplex hw .H (archDerivAtComplex hw .E φ)
          - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) = (2 : ℂ) • archDerivAtComplex hw .E φ) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ)
          - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) = -((2 : ℂ) • archDerivAtComplex hw .Fm φ)) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ)
          - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) = archDerivAtComplex hw .H φ) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ)
          - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) = 0) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) = (2 : ℂ) • archDerivAtComplex hw .iE φ) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) = -((2 : ℂ) • archDerivAtComplex hw .iFm φ)) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ)
          - archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) = -((2 : ℂ) • archDerivAtComplex hw .iE φ)) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) = 0) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) = archDerivAtComplex hw .iH φ) ∧
      (archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ)
          - archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) = (2 : ℂ) • archDerivAtComplex hw .iFm φ) ∧
      (archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) = -archDerivAtComplex hw .iH φ) ∧
      (archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) = 0) ∧
      (archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) = -((2 : ℂ) • archDerivAtComplex hw .E φ)) ∧
      (archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) = (2 : ℂ) • archDerivAtComplex hw .Fm φ) ∧
      (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) = -archDerivAtComplex hw .H φ)) := by sorry
