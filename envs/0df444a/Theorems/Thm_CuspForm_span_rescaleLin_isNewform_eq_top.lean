-- Prove2me | Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
-- name    : CuspForm.span_rescaleLin_isNewform_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/b728f795-ff63-5600-a22b-581e83211395
-- title:
--   Rescaled newforms span the weight-2 cusp forms for Γ₀(M)
-- statement:
--   Let $M$ be a natural number which is nonzero. Consider the complex vector space $\mathrm{CuspForm}(\Gamma_0(M),2)$ of weight-$2$ cusp forms for the congruence subgroup $\Gamma_0(M)$, and inside it the set of those $F$ for which there exist natural numbers $R$ and $d$ with $d\cdot R \mid M$ and a weight-$2$ cusp form $g$ for $\Gamma_0(R)$ such that $g$ satisfies [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23) and $F$ is the image of $g$ under the degeneracy map [`FreyPackage.ModMCarrier.rescaleLin`](def/FreyPackage_ModMCarrier_Rescale.html#L140) attached to the divisibility $d\cdot R \mid M$ in weight $2$, that is, the slash of $g$ in weight $2$ by the matrix `heckeDiagMatrix` $d$ (the scaling $\tau \mapsto d\tau$ in bundled form). Here [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23) for $g$ of level $R$ means: $g$ is a normalized eigenform, i.e. its $q$-coefficient at $1$ is $1$, its $q$-coefficients are multiplicative at coprime arguments, they satisfy the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for primes $p \nmid R$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for primes $p \mid R$; and moreover for no proper divisor $M' \mid R$, $M' \neq R$, does there exist a normalized eigenform of level $M'$ whose $q$-coefficients at all primes $\ell \nmid R$ agree with those of $g$. The assertion is that the $\mathbb{C}$-span of this set is all of $\mathrm{CuspForm}(\Gamma_0(M),2)$. Only spanning is asserted; no independence or direct-sum statement is made.
--
--   This is the spanning half of the Atkin–Lehner–Li old/new description of the space of weight-$2$ cusp forms of level $M$: every cusp form is a linear combination of rescalings of newforms of levels dividing $M$. It is used downstream to compute Hecke eigenspaces attached to a newform, for instance to identify the simultaneous eigenspace of the Hecke operators with the line spanned by the newform and to determine its dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_span_rescaleLin_isNewform_eq_top.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.span_rescaleLin_isNewform_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ
      {F : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
        ∃ (R d : ℕ) (hdRM : d * R ∣ M) (g : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
          CuspForm.IsNewform g ∧ F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g} = ⊤ := by sorry
