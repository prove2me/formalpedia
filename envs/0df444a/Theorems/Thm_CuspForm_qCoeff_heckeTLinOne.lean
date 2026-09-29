-- Prove2me | Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
-- name    : CuspForm.qCoeff_heckeTLinOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/0093c64f-3f8b-5ddd-a46e-58c69c78ccea
-- title:
--   q-expansion of Tₚ on S_k(Γ₁(M))
-- statement:
--   Let $M$ be a natural number, $k$ an integer, $p$ a prime with $p \nmid M$, $f$ a cusp form of weight $k$ for $\Gamma_1(M)$, and $n$ a natural number. Write $a_m(g) =$ [`ModularFormClass.qCoeff g m`](def/FLTPrelim_Modularity.html#L19) for the $m$-th coefficient of the $q$-expansion of period $1$ of $g$. The Hecke operator [`CuspForm.heckeTLinOne k hp hpM`](def/CuspForm_Gamma1HeckeOperators.html#L652) is the linear endomorphism of $S_k(\Gamma_1(M))$ whose underlying function on $f$ is $U_p f + (\langle p\rangle f)\mid_k \mathrm{diag}(p,1)$, where $U_p$ is [`ModularForm.heckeU k p`](def/ModularForm_HeckeOperator.html#L93) and $\langle p\rangle =$ [`CuspForm.diamondLinOne M k p`](def/CuspForm_Gamma1HeckeOperators.html#L592) is slashing by a chosen $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ with lower-right entry congruent to $p$ modulo $M$ (the identity map if no such $\gamma$ exists). The assertion is the coefficient identity
--   $$a_n(T_p f) = a_{pn}(f) + p^{\,k-1}\bigl(\text{$a_{n/p}(\langle p\rangle f)$ if $p \mid n$, else $0$}\bigr),$$
--   with $p^{\,k-1}$ the integer power of $p$ in $\mathbb{C}$ and $n/p$ natural-number division.
--
--   This is the classical formula for the action of $T_p$ on $q$-expansions at $\infty$ for forms on $\Gamma_1(M)$, with the diamond operator $\langle p\rangle$ appearing in the second term; for a form of nebentypus $\varepsilon$ it specialises to $a_n(T_pf) = a_{pn}(f) + \varepsilon(p)p^{k-1}a_{n/p}(f)$. It is used downstream to translate operator-level eigenform conditions into relations among $q$-coefficients, in particular for Hecke eigenvalue systems, nebentypus normalisations and primitive forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_heckeTLinOne.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_Gamma1HeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.qCoeff_heckeTLinOne {M : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLinOne k hp hpM f) n =
      ModularFormClass.qCoeff f (p * n) +
        (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff (CuspForm.diamondLinOne M k p f) (n / p) else 0) := by sorry
