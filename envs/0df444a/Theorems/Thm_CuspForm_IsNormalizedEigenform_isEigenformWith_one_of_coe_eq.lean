-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq
-- name    : CuspForm.IsNormalizedEigenform.isEigenformWith_one_of_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/a36b4abc-7fe2-562f-bf02-3f1fcfe40de4
-- title:
--   Normalised Γ₀(N) eigenform as trivial-nebentypus Γ₁(N) eigenform
-- statement:
--   Let $N$ be a natural number and let $g$ be a cusp form of weight $2$ for $\Gamma_0(N)$ satisfying the predicate `IsNormalizedEigenform`, i.e. writing $a_n =$ `qCoeff` $g\,n$ for the $n$-th coefficient of the $q$-expansion of width $1$: $a_1 = 1$; $a_{mn} = a_m a_n$ whenever $m$ and $n$ are coprime; $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for every prime $p$ with $p \nmid N$ and every $r$; and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for every prime $p$ with $p \mid N$ and every $r$. Let $g_1$ be a cusp form of weight $2$ for $\Gamma_1(N)$ whose underlying function $\mathbb{H} \to \mathbb{C}$ equals that of $g$. The conclusion is `IsEigenformWith` for $g_1$ with the trivial Dirichlet character $1$ modulo $N$, which unfolds to four assertions about $b_n =$ `qCoeff` $g_1\,n$: $b_1 = 1$; for every prime $p \nmid N$ and every $n$, $b_{pn} + 1(p)\,p^{2-1}\,[p \mid n]\,b_{n/p} = b_p b_n$; for every prime $\ell \mid N$ and every $n$, $b_{\ell n} = b_\ell b_n$; and the nebentypus relation $g_1(\gamma \tau) = 1(d)\bigl((c\tau + d)^2 g_1(\tau)\bigr)$ for all $\gamma \in \Gamma_0(N)$ and $\tau \in \mathbb{H}$, where $c = \gamma_{10}$, $d = \gamma_{11}$ and the character is evaluated at $d \bmod N$.
--
--   This is the passage between the two standard coefficient descriptions of a normalised Hecke eigenform: the multiplicative-plus-prime-power-recursion form on $\Gamma_0(N)$, and the form in which the Hecke relations are stated for $\Gamma_1(N)$ with a nebentypus character, here the trivial one. It is used in the construction of the associated adelic automorphic object, being cited by [`CuspForm.IsNormalizedEigenform.isIsotypicCuspFormAt_one_of_isAdelicLiftOf`](thm.html#CuspForm.IsNormalizedEigenform.isIsotypicCuspFormAt_one_of_isAdelicLiftOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq.lean

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
open scoped ModularForm

theorem CuspForm.IsNormalizedEigenform.isEigenformWith_one_of_coe_eq
    {N : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform)
    (g₁ : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hg₁ : (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g) :
    CuspForm.IsEigenformWith (1 : DirichletCharacter ℂ N) g₁ := by sorry
