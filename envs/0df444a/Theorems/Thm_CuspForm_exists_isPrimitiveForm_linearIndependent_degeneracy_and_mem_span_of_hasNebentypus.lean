-- Prove2me | Theorems.Thm_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus
-- name    : CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/07bd49e0-6d17-5cd0-a12a-c191b91cc58c
-- title:
--   Atkin–Lehner–Li basis of S_k(M,ε) from primitive forms
-- statement:
--   Fix $M\ge 1$, a weight $k\in\mathbb Z$ and a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb C$. The assertion is the existence of an $n\in\mathbb N$, levels $L_i\mid M$ for $i\in\{0,\dots,n-1\}$, characters $\varepsilon_i$ modulo $L_i$, cusp forms $g_i$ of weight $k$ on $\Gamma_1(L_i)$, and cusp forms $G_{i,d}$ of weight $k$ on $\Gamma_1(M)$ indexed by $i$ and by a natural number $d$, with the following properties. Each $g_i$ is a primitive form for $\varepsilon_i$, in the sense of [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38): its first $q$-coefficient is $1$, the Hecke recursion $a_{pn}+\varepsilon_i(p)p^{k-1}a_{n/p}=a_pa_n$ holds for primes $p\nmid L_i$, $a_{\ell n}=a_\ell a_n$ for primes $\ell\mid L_i$, $g_i$ transforms under $\Gamma_0(L_i)$ by $g_i(\gamma\tau)=\varepsilon_i(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^k g_i(\tau)$, and for no proper divisor $M'$ of $L_i$ does the eigenpacket $(a_n(g_i),\varepsilon_i)$ occur at level $M'$ (no nonzero cusp form of weight $k$ on $\Gamma_1(M')$ with some nebentypus agreeing with $\varepsilon_i$ and satisfying the same Hecke recursion at all primes outside a finite set). For $i\ne j$ one has $L_i\ne L_j$ or some $q$-coefficient of $g_i$ differs from that of $g_j$; each $\varepsilon_i$ induces $\varepsilon$ under `DirichletCharacter.changeLevel`; and the list is complete: any primitive form $g'$ for a character $\varepsilon'$ modulo a divisor $L'$ of $M$ whose induced character is $\varepsilon$ satisfies $L_i=L'$ and has the same $q$-coefficients as $g_i$ for some $i$. For every $d\mid M/L_i$ one has $G_{i,d}(\tau)=g_i(d\tau)$ (the action of [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21) $d$ on the upper half-plane) and $G_{i,d}$ has nebentypus $\varepsilon$ for $\Gamma_0(M)$. Finally the family $(G_{i,d})$, indexed by pairs $(i,d)$ with $d$ a divisor of $M/L_i$, is linearly independent over $\mathbb C$, and every cusp form $f$ of weight $k$ on $\Gamma_1(M)$ with nebentypus $\varepsilon$ lies in the $\mathbb C$-span of its range.
--
--   This is the Atkin–Lehner–Li decomposition of the nebentypus eigenspace $S_k(M,\varepsilon)$ into the degeneracy images $g(d\tau)$ of the primitive forms of divisor level whose character induces $\varepsilon$, packaged as an explicit spanning and linearly independent family. It underlies the subsequent description of the newform eigenspaces and of Hecke-eigenform bases for the groups $\Gamma_H$, namely [`CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace`](thm.html#CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace) and [`CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply`](thm.html#CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus.lean

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (εL : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k),
      (∀ i, CuspForm.IsPrimitiveForm (εL i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, DirichletCharacter.changeLevel (hL i) (εL i) = ε) ∧
      (∀ (L' : ℕ) [NeZero L'] (hL' : L' ∣ M) (ε' : DirichletCharacter ℂ L')
          (g' : CuspForm (CongruenceSubgroup.Gamma1 L') k),
        CuspForm.IsPrimitiveForm ε' g' → DirichletCharacter.changeLevel hL' ε' = ε →
        ∃ i, L i = L' ∧ ∀ m : ℕ, ModularFormClass.qCoeff (g i) m = ModularFormClass.qCoeff g' m) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
        CuspForm.HasNebentypus ε (G i d)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      (∀ f : CuspForm (CongruenceSubgroup.Gamma1 M) k, CuspForm.HasNebentypus ε f →
        f ∈ Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ))) := by sorry
