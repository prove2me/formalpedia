-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile
-- name    : AutomorphicForm.convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ff9532e8-8ee7-54c9-870c-151d5894a730
-- title:
--   Right convolution commutes with pseudo-Eisenstein series
-- statement:
--   Let $F$ be a number field, let $Z$ be a subgroup of the group of units of the adele ring of $F$, and let $\xi : Z \to \mathbb{C}^\times$ be a homomorphism all of whose values have absolute value $1$. Let $\psi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $F$ which is a slab profile for $(Z,\xi)$ in the sense of `IsSlabProfile`: $\psi$ is measurable for the Borel structure on $\mathrm{GL}_2(\mathbb{A})$; $\psi(n(x)g) = \psi(g)$ for every adele $x$, where $n(x)$ is the upper triangular unipotent matrix with entry $x$; $\psi(\gamma g) = \psi(g)$ for every $\gamma$ in the subgroup of $\mathrm{GL}_2(F)$ of matrices with vanishing lower-left entry, embedded into $\mathrm{GL}_2(\mathbb{A})$; $\psi(z g) = \xi(z)\psi(g)$ for $z \in Z$ acting by the corresponding scalar matrix; for all $d_1 > 0$ and $d_2$ there is a bound $C$ with $\|\psi(g)\| \le C$ whenever the idele norm (the module of the distributive Haar character) of $\det g$ lies in $[d_1,d_2]$; and there are $a > 0$ and $b$ such that $\psi(g) \neq 0$ forces the adelic height of $g$ to lie in $[a,b]$. Let $f$ be continuous with compact support, and let $g \in \mathrm{GL}_2(\mathbb{A})$. Then, with $(R(f)u)(g) = \int u(gx) f(x)\,dx$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A})$ and with the pseudo-Eisenstein series $\theta_\varphi(g) = \varphi(g) + \sum_{\beta \in F}' \varphi(w\, n(\beta)\, g)$, where $w$ is the image of the Weyl element of $\mathrm{GL}_2(F)$ and the sum is the unconditional $\mathrm{tsum}$, one has $(R(f)\theta_\psi)(g) = \theta_{R(f)\psi}(g)$.
--
--   This is the standard interchange of a right convolution operator with the Bruhat sum defining a pseudo-Eisenstein series, $R(f)\theta_\psi = \theta_{R(f)\psi}$, for profiles constrained to a band of the adelic height. It is used by [`AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite`](thm.html#AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite), where the convolution algebra is made to act on the space of such series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile.lean

import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isSlabProfile
    (F : Type) [Field F] [NumberField F]
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (hξu : ∀ z : Z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (_hψ : AutomorphicForm.IsSlabProfile F Z ξ ψ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (g : AdelicGL2 (𝓞 F) F) :
    convOp F f (AutomorphicForm.pseudoEisenstein F ψ) g =
      AutomorphicForm.pseudoEisenstein F (convOp F f ψ) g := by sorry
