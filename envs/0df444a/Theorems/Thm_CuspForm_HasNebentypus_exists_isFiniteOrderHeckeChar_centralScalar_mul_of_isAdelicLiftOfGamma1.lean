-- Prove2me | Theorems.Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
-- name    : CuspForm.HasNebentypus.exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/664b5093-2581-52ea-a580-8d9291b15790
-- title:
--   Central character of the adelic lift of a nebentypus form
-- statement:
--   Let $M\ge 1$ be an integer, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb C$, and $h$ a cusp form of weight $2$ for $\Gamma_1(M)$ having nebentypus $\varepsilon$, i.e. $h(\gamma\tau)=\varepsilon(\gamma_{11}\bmod M)\bigl((\gamma_{10}\tau+\gamma_{11})^{2}h(\tau)\bigr)$ for all $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lying in $\Gamma_0(M)$ and all $\tau$ in the upper half-plane. Let $\Phi\colon \mathrm{GL}_2(\mathbb A_{\mathbb Q})\to\mathbb C$ be an adelic lift of $h$ of level $M$: $\Phi$ is left invariant under the image of $\mathrm{GL}_2(\mathbb Q)$, right invariant under the image in $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ of the level-one subgroup `finiteLevelOne` of $\mathrm{GL}_2$ of the finite adeles attached to the ideal $(M)$ of $\mathcal O_{\mathbb Q}$, and at any $g$ with trivial finite part and $\mathrm{ratArchGL2}\,g\in\mathrm{GL}_2^{+}(\mathbb R)$ one has $\Phi(g)=\bigl(h\mid_{2}\mathrm{ratArchGL2}\,g\bigr)(i)$. Then there is a group homomorphism $\omega\colon \mathbb A_{\mathbb Q}^{\times}\to\mathbb C^{\times}$ which (i) is trivial on principal ideles, continuous and of finite order; (ii) admits the modulus $(M)$, i.e. $\omega(u)=1$ for every idele unit $u$ with archimedean part $1$ whose finite components satisfy $v(u_v)=1$ and $v(u_v-1)\le\exp(-\mathrm{ord}_v(M))$ at every finite place $v$; (iii) satisfies $\omega(\varpi_\ell)=\varepsilon(\ell\bmod M)$ for every prime $\ell\nmid M$, where $\varpi_\ell$ is the uniformiser idele at the place of $\mathbb Q$ attached to $\ell$; and (iv) gives the action of the centre on $\Phi$: $\Phi(\mathrm{diag}(z,z)\,x)=\omega(z)\,\Phi(x)$ for all $z\in\mathbb A_{\mathbb Q}^{\times}$ and all $x\in\mathrm{GL}_2(\mathbb A_{\mathbb Q})$.
--
--   This is the passage from the nebentypus of a weight-two form on $\Gamma_1(M)$ to the central character of its adelic lift, realised as a finite-order Hecke character of $\mathbb Q$ of modulus $(M)$ whose values at unramified uniformisers are those of $\varepsilon$. It is used in the identification of the adelic span attached to a newform with its primitive adelic lift and twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_HasNebentypus_exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem CuspForm.HasNebentypus.exists_isFiniteOrderHeckeChar_centralScalar_mul_of_isAdelicLiftOfGamma1
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ ω ∧
      HeckeCharacter.AdmitsModulus ℚ ω (AdelicDock.ratLevel M) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
        (ω (uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) = ε (ℓ : ZMod M)) ∧
      ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
        Φ (centralScalar (𝓞 ℚ) ℚ z * x) = (ω z : ℂ) * Φ x := by sorry
