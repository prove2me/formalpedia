-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral
-- name    : AutomorphicForm.constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/839c2042-1715-5d09-9fc2-cdfda80fc6cb
-- title:
--   Constant term of a pseudo-Eisenstein series of a slab profile
-- statement:
--   Let $F$ be a number field, $\mathbb{A}$ its adele ring, $Z$ a subgroup of the idele group $\mathbb{A}^\times$ and $\xi\colon Z \to \mathbb{C}^\times$ a character. Let $\varphi\colon \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ satisfy `IsSlabProfile`, i.e. $\varphi$ is measurable, invariant under left multiplication by the unipotent matrices $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ ($x \in \mathbb{A}$) and by the images of the $F$-points of the Borel subgroup (lower left entry zero), transforms by $\xi(z)$ under left multiplication by the central scalar of $z \in Z$, is bounded on each slab $d_1 \le \|\det g\|_{\mathbb{A}} \le d_2$ with $d_1 > 0$, and vanishes outside a band $a \le \mathrm{ht}(g) \le b$ with $a>0$ for the adelic height. Fix $g \in \mathrm{GL}_2(\mathbb{A})$. Writing $\theta_\varphi(h) = \varphi(h) + \sum_{\beta \in F} \varphi(w\, n(\beta)\, h)$ for the pseudo-Eisenstein series attached to $\varphi$, with $w$ the image of the Weyl element, and $\mathcal{B} \subseteq \mathbb{A}$ for the adelic box (infinite box times the integral finite adeles), the assertion is $$\int_{\mathbb{A}} \theta_\varphi(n(x)g)\, d\mu_{\mathcal{B}}(x) = \varphi(g) + \mathrm{vol}(\mathcal{B})^{-1}\int_{\mathbb{A}} \varphi(w^{-1} n(x) g)\, dx,$$ where $dx$ is the additive Haar measure of $\mathbb{A}$ for the Borel structure, $\mathrm{vol}(\mathcal{B})$ is its value on $\mathcal{B}$, and $\mu_{\mathcal{B}}$ is that measure conditioned on $\mathcal{B}$.
--
--   This is the standard computation of the constant term along the unipotent radical of an incomplete theta (pseudo-Eisenstein) series: the $F$-sum over unipotent translates unfolds against a fundamental domain for $F$ in $\mathbb{A}$ to give the full adelic intertwining integral, normalised by the volume of the box. It is used in the subsequent computation of the integral of a pseudo-Eisenstein series against the conjugate of another over a slab, [`AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_pseudoEisenstein_eq_setIntegral_quotient_slab`](thm.html#AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_pseudoEisenstein_eq_setIntegral_quotient_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

theorem AutomorphicForm.constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral
    (F : Type) [Field F] [NumberField F]
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (_hφ : AutomorphicForm.IsSlabProfile F Z ξ φ)
    (g : AdelicGL2 (𝓞 F) F) :
    letI := adeleBorel (𝓞 F) F
    constantTerm (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
        unipotentGL2 (AutomorphicForm.pseudoEisenstein F φ) g
      = φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by sorry
