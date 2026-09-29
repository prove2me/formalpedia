-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_sum_apply_padicToAdelic_eq_mul_of_mem_span_fnTwist
-- name    : CuspForm.IsNormalizedEigenform.sum_apply_padicToAdelic_eq_mul_of_mem_span_fnTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/b7cbb91a-b2f4-5507-af1a-5e2d3939548b
-- title:
--   Hecke eigenvalue η(varpi_ℓ)⁻¹a_ℓ(g) on the twisted adelic span
-- statement:
--   Let $M\ge 1$ and let $g$ be a weight-two cusp form on $\Gamma_0(M)$ which is a normalized eigenform in the sense of `IsNormalizedEigenform`: its first $q$-expansion coefficient is $1$, the coefficients are multiplicative on coprime indices, and they satisfy the recursions $a_{p^{r+2}}=a_pa_{p^{r+1}}-p\,a_{p^r}$ for primes $p\nmid M$ and $a_{p^{r+2}}=a_pa_{p^{r+1}}$ for $p\mid M$. Let $\Phi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be an adelic lift of $g$, i.e. $\Phi$ is left invariant under the global points $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the finite level-one subgroup of the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, and on elements $h$ with trivial finite part and totally positive archimedean part satisfies $\Phi(h)=(g\mid[2]\,h_\infty)(i)$. Let $q$ be a prime and $\eta:\mathbb{A}_{\mathbb{Q}}^{\times}\to\mathbb{C}^{\times}$ a character admitting the modulus $(q^b)$, i.e. $\eta(u)=1$ for every idele unit $u$ with archimedean component $1$, all finite components of valuation $1$ and $v(u_v-1)\le\exp(-\mathrm{ord}_v(q^b))$ at every finite place $v$. Let $\ell$ be a prime with $\ell\nmid M$ and $\ell\neq q$, and let $\rho_0,\dots,\rho_\ell\in\mathrm{GL}_2(\mathbb{Q}_\ell)$ be given by $\rho_i=\begin{pmatrix}1&i\\0&\ell\end{pmatrix}$ for $i<\ell$ and $\rho_\ell=\begin{pmatrix}\ell&0\\0&1\end{pmatrix}$. Write $\Phi'=$ `fnTwist ℚ η Φ`, the pointwise product of $\Phi$ with $\eta\circ\det$. Then for every $y$ in the span type `AdelicSpan` $\Phi'$ which lies in the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished element `self` attached to $\Phi'$, and every $x\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the associated function $y$ satisfies $$\sum_{i=0}^{\ell} y\bigl(x\cdot\iota_\ell(\rho_i^{-1})\bigr)=\eta(\varpi_\ell)^{-1}\,a_\ell(g)\,y(x),$$ where $\iota_\ell$ is the embedding [`AdelicDock.padicToAdelic`](def/AdelicDock_LocalEmbedding.html#L254) of $\mathrm{GL}_2(\mathbb{Q}_\ell)$ into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ at the place of $\ell$, $\varpi_\ell$ is the idele which is a uniformizer at that place and $1$ elsewhere, and $a_\ell(g)$ is the $\ell$-th coefficient of the $q$-expansion of $g$.
--
--   This is the statement that the adelic Hecke operator attached to the double coset of $\mathrm{diag}(\ell,1)$ at a prime $\ell\nmid Mq$ acts on the whole $\mathrm{GL}_2(\mathbb{Q}_q)$-span of the $\eta$-twisted adelic lift of $g$ by the scalar $\eta(\varpi_\ell)^{-1}a_\ell(g)$, the twist by an unramified-at-$\ell$ character multiplying the eigenvalue by $\eta(\varpi_\ell)^{-1}$. It feeds the construction of a form of $\Gamma_1$-level with prescribed nebentypus and prescribed Hecke eigenvalues out of the twisted span, and the accompanying linear relation for newforms in that span.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_sum_apply_padicToAdelic_eq_mul_of_mem_span_fnTwist.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.sum_apply_padicToAdelic_eq_mul_of_mem_span_fnTwist
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hℓq : ℓ ≠ q)
    (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1])
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∑ i : Fin (ℓ + 1), (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn
        (x * AdelicDock.padicToAdelic ℓ (ρ i)⁻¹) =
      ((η (AutomorphicForm.uniformizerIdele ℚ (AdelicDock.padicPlace ℓ)) : ℂ)⁻¹ *
          ModularFormClass.qCoeff g ℓ) *
        (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn x := by sorry
