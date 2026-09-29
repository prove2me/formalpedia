-- Prove2me | Theorems.Thm_CuspForm_IsNewform_adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist
-- name    : CuspForm.IsNewform.adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/df0f2ad9-7272-59e8-b828-fba3622b3aa5
-- title:
--   Multiplicity one: twisted newform lift and primitive form span
-- statement:
--   Fix $M \ge 1$ and a weight-two cusp form $g$ on $\Gamma_0(M)$ which is a newform in the sense of [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23): $g$ is a normalised eigenform and no good eigensystem for $g$ occurs at a proper divisor of $M$. Let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ that is an adelic lift of $g$, i.e. invariant under left multiplication by global points of $\mathrm{GL}_2(\mathbb{Q})$, invariant under right multiplication by the finite level-one subgroup attached to the ideal $(M)$, and given by $(g \mid_2 h_\infty)(i)$ at every $h$ whose finite part is trivial and whose archimedean part has positive determinant. Let $q$ be prime, let $\eta$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ which is a finite-order Hecke character (trivial on global units, continuous, of finite order) admitting the modulus $(q^{b})$ for some $b$. Let $M' \ge 1$, let $\varepsilon$ be a Dirichlet character mod $M'$ and let $h$ be a weight-two cusp form on $\Gamma_1(M')$ which is primitive for $\varepsilon$: an eigenform with nebentypus $\varepsilon$ whose eigenpacket of $q$-expansion coefficients and character values occurs at no proper divisor of $M'$. Let $\Phi_h$ be an adelic lift of $h$ in the corresponding $\Gamma_1$ sense (left $\mathrm{GL}_2(\mathbb{Q})$-invariance, right invariance under the finite level-one subgroup of $(M')$, and the same archimedean normalisation). Assume that for every prime $\ell$ dividing neither $M$ nor $M'$ and distinct from $q$ one has $a_\ell(h) = \eta(\varpi_\ell)\, a_\ell(g)$ and $\varepsilon(\ell) = \eta(\varpi_\ell)^2$, where $a_\ell$ denotes the $\ell$-th $q$-expansion coefficient and $\varpi_\ell$ the idele with a uniformiser at the place of $\mathbb{Q}$ above $\ell$ and $1$ elsewhere. Then the $\mathbb{C}$-span of the right translates of $\Phi_h$ in the carrier of adelic functions coincides with the $\mathbb{C}$-span of the right translates of the twist $g \mapsto \chi_{\det}(\eta)(g)\,\Phi(g)$ of $\Phi$ by $\eta$ composed with the determinant.
--
--   This is the strong multiplicity one statement used in the twisting step: a newform whose Hecke eigenvalues and central character agree with those of the $\eta$-twist of $g$ outside $MM'q$ generates, adelically, the same automorphic representation as that twist. It feeds the construction of a primitive form whose associated adelic lift has unramified local behaviour at the relevant place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNewform.adelicSpanSubmodule_eq_of_isPrimitiveForm_adelicLiftGamma1_fnTwist
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    {M' : ℕ} [NeZero M'] {ε : DirichletCharacter ℂ M'} {h : CuspForm (CongruenceSubgroup.Gamma1 M') 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (Φh : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φh)
    (ha : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ¬ ℓ ∣ M' → ℓ ≠ q →
      ModularFormClass.qCoeff h ℓ =
        (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) * ModularFormClass.qCoeff g ℓ)
    (hε : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ¬ ℓ ∣ M' → ℓ ≠ q →
      ε (ℓ : ZMod M') = (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) ^ 2) :
    LocalNewvector.AdelicSpanSubmodule Φh = LocalNewvector.AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ) := by sorry
