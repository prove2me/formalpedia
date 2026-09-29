-- Prove2me | Theorems.Thm_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated
-- name    : CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/010c3f59-6542-590f-9901-255b22ae3f2a
-- title:
--   Integral q-expansion map on S_k(Γ₀(N);ℤ) is saturated
-- statement:
--   Fix a natural number $N$ (nonzero) and a weight $k \in \mathbb Z$, and let $L =$ [`CuspForm.intLattice N k`](def/CuspForm_IntegralStructure.html#L3) be the $\mathbb Z$-submodule of $\mathbb C$-cusp forms of weight $k$ for $\Gamma_0(N)$ spanned by those forms $f$ all of whose $q$-expansion coefficients $\mathrm{qCoeff}\,f\,n$ — the coefficients of the $q$-expansion of $f$ with respect to period $1$ — lie in the image of $\mathbb Z \to \mathbb C$. The assertion is that there exists an additive monoid homomorphism $a : L \to (\mathbb N \to \mathbb Z)$ with three properties. First, $a$ computes $q$-coefficients: for every $f \in L$ and every $n \in \mathbb N$, the image of the integer $a\,f\,n$ in $\mathbb C$ equals $\mathrm{qCoeff}$ of the underlying cusp form of $f$ at $n$. Second, $a$ is injective. Third, $a$ is saturated in the following sense: for every integer $m$ (including $m = 0$) and every $f \in L$, if $m$ divides $a\,f\,n$ in $\mathbb Z$ for all $n$, then $f = m \cdot g$ for some $g \in L$.
--
--   This is the elementary, forms-side half of the mod-$m$ $q$-expansion principle for $\Gamma_0(N)$: the integral lattice of cusp forms injects coefficientwise into $\mathbb Z^{\mathbb N}$ and the image is saturated, so that reduction modulo $m$ remains injective. It is used downstream in the construction of base-changed integral $q$-expansion maps and in the dimension and Hecke-operator estimates for mod-$p$ cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_QCoeffLinear

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ a : ↥(CuspForm.intLattice N k) →+ (ℕ → ℤ),
      (∀ (f : ↥(CuspForm.intLattice N k)) (n : ℕ),
        ((a f n : ℤ) : ℂ) = ModularFormClass.qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) n) ∧
      Function.Injective a ∧
      ∀ (m : ℤ) (f : ↥(CuspForm.intLattice N k)), (∀ n, m ∣ a f n) →
        ∃ g : ↥(CuspForm.intLattice N k), f = m • g := by sorry
