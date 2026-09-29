-- Prove2me | Theorems.Thm_CuspForm_exists_finite_separated_newform_family
-- name    : CuspForm.exists_finite_separated_newform_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/4720bfd0-0e6c-573e-8dff-43eedc4b3754
-- title:
--   Finite family of newforms spanning S₂(Γ₀(M)), separated at good primes
-- statement:
--   Let $M$ be a natural number, assumed nonzero. Then there exist a type $\iota$ equipped with a `Fintype` instance, a family of levels $N : \iota \to \mathbb{N}$ with $N_i \mid M$ for every $i$, and for each $i$ a weight-$2$ cusp form $g_i$ on $\Gamma_0(N_i)$, such that three conditions hold. First, each $g_i$ satisfies [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23): it is a normalised eigenform, meaning its $q$-expansion coefficients (the coefficients of `qExpansion 1`) satisfy $a_1 = 1$, $a_{mn} = a_m a_n$ for coprime $m,n$, the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^{r}}$ for primes $p \nmid N_i$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for primes $p \mid N_i$; and it is new, in that no proper divisor $M' \mid N_i$, $M' \neq N_i$, carries a normalised eigenform whose $\ell$-th coefficient agrees with that of $g_i$ for all primes $\ell \nmid N_i$. Second, the $\mathbb{C}$-span of the set of all forms of the shape $\mathrm{rescaleLin}(h)_2(g_i)$, for $i \in \iota$ and $d \in \mathbb{N}$ with $h : d\,N_i \mid M$ — that is, the degeneracy maps $f \mapsto f \mid_2 \mathrm{heckeDiagMatrix}\,d$ — is the whole space of weight-$2$ cusp forms on $\Gamma_0(M)$. Third, the family is pairwise separated away from $M$: for $i \neq j$ there is a prime $\ell$ with $\ell \nmid M$ and $a_\ell(g_i) \neq a_\ell(g_j)$.
--
--   This packages the oldform–newform decomposition of $S_2(\Gamma_0(M))$ in the form needed later: a finite list of newforms of divisor level whose degeneracy translates span the full space, with distinct members distinguished already by a single Hecke eigenvalue at a prime not dividing $M$. It is used by [`CuspForm.exists_cyclic_span_heckeAlgebra`](thm.html#CuspForm.exists_cyclic_span_heckeAlgebra) and by [`CuspForm.exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level`](thm.html#CuspForm.exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_finite_separated_newform_family.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_finite_separated_newform_family (M : ℕ) [NeZero M] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → ℕ) (hN : ∀ i, N i ∣ M)
      (g : ∀ i, CuspForm (CongruenceSubgroup.Gamma0 (N i)) 2),
      (∀ i, CuspForm.IsNewform (g i)) ∧
      Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
        ∃ (i : ι) (d : ℕ) (h : d * N i ∣ M), F = FreyPackage.ModMCarrier.rescaleLin h 2 (g i)} = ⊤ ∧
      (∀ i j, i ≠ j → ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ M ∧
        ModularFormClass.qCoeff (g i) ℓ ≠ ModularFormClass.qCoeff (g j) ℓ) := by sorry
