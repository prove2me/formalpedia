-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
-- name    : CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/be3514a9-a995-57aa-bf2f-e0e79f0e32c2
-- title:
--   Adelic lift of a weight-two Γ₁(M) eigenform is isotypic
-- statement:
--   Let $M$ be a nonzero natural number, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and $h$ a cusp form of weight $2$ for $\Gamma_1(M)$ which is an eigenform with character $\varepsilon$, i.e. $a_1(h)=1$, for every prime $p\nmid M$ and every $n$ one has $a_{pn}(h)+\varepsilon(p)p^{k-1}[p\mid n]a_{n/p}(h)=a_p(h)a_n(h)$ with $k=2$, $a_{\ell n}(h)=a_\ell(h)a_n(h)$ for primes $\ell\mid M$, and $h$ has nebentypus $\varepsilon$. Let $\Phi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be an adelic lift of $h$: invariant on the left under the image of $\mathrm{GL}_2(\mathbb{Q})$, invariant on the right under the finite level-one group of the ideal $(M)=\mathrm{span}\{M\}\subseteq\mathcal{O}_{\mathbb{Q}}$ embedded at the finite places, and with $\Phi(x)=(h\mid_2 x_\infty)(i)$ whenever the finite part of $x$ is trivial and $x_\infty\in\mathrm{GL}_2^+(\mathbb{R})$. Let $\xi$ be a homomorphism from the centre group $Z$ of the general production pins of $\mathbb{Q}$ to $\mathbb{C}^\times$ with $\Phi(\mathrm{diag}(z,z)x)=\xi(z)\Phi(x)$ for all $z\in Z$. Let $S$ be a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$ such that no $v\notin S$ divides $(M)$, and let $\Psi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex entries (a nonzero level ideal together with functions $a,b$ on primes) satisfying, for all $v\notin S$, $\Psi.a\,v=a_{N(v)}(h)$ and $\Psi.b\,v=N(v)\,\varepsilon(N(v)\bmod M)$, where $N(v)$ is the absolute norm of $v$. Then $\Phi$ is an isotypic cusp form at the general production pins of $\mathbb{Q}$ with data $(\xi,(M),S,\Psi)$; unfolding, $\Phi$ is a smooth cusp automorphic function at those pins with central character $\xi$ (membership in the $\xi$-isotypic $L^2$ space over the pins' window, cuspidality along the unipotent subgroup, and $K_f$-smoothness), $\Phi$ is continuous, $\Phi(gu)=\Phi(g)$ for all $g$ and all $u$ in the pins' level subgroup at $(M)$, for every $v\notin S$ there is a system of $N(v)+1$ coset representatives for the Hecke generator at $v$ relative to that level subgroup whose coset sum applied to $\Phi$ equals $\Psi.a\,v\cdot\Phi$, and for every $v\notin S$ and all $g$ one has $\Phi(\mathrm{diag}(d,d)g)=(\mathrm{cNorm}\,v)^{-1}\Psi.b\,v\cdot\Phi(g)$, where $d$ is the determinant of the Hecke generator at $v$.
--
--   This is the weight-two classical-to-adelic dictionary: it converts a normalised Hecke eigenform on $\Gamma_1(M)$ with nebentypus, together with an adelic lift of it, into an automorphic form on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ satisfying the isotypic-cusp-form axioms at the pins of the general production datum (Siegel-set window with parameters $(1/2,1,1/2,2)$, level family $N\mapsto U_1(N)$, Hecke generators $\mathrm{diag}(\varpi_v,1)$). It feeds the multiplicity-one and newform-span arguments, being cited in the identification of the adelic span of a primitive form and in the normalised-eigenform case of the same bridge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (hξ : ∀ (z : ↥((productionPinsGeneral ℚ).Z)) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      Φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * x) = ((ξ z : ℂˣ) : ℂ) * Φ x)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ AdelicDock.ratLevel M)
    (Ψ : HeckeEigensystem ℚ ℂ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.a v = ModularFormClass.qCoeff h (Ideal.absNorm v.asIdeal))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.b v = (Ideal.absNorm v.asIdeal : ℂ) * ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M)) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ (AdelicDock.ratLevel M) S Ψ Φ := by sorry
