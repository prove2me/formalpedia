-- Prove2me | Theorems.Thm_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
-- name    : DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/40886a72-5292-5fbb-96eb-28b60acdbe6c
-- title:
--   Rankin's second-moment bound for weight-one Hecke eigenforms
-- statement:
--   Let $N$ be a nonzero natural number, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and let $f$ be a cusp form of weight $1$ for $\Gamma_1(N)$. Write $a_n =$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of $f$ taken with period $1$ (the coefficient of index $n$ in `qExpansion 1 f`). Assume $a_1 = 1$, and assume the Hecke eigenvector relations away from $N$: for every prime $p$ not dividing $N$ and every natural number $n$,
--   $$a_{pn} + \varepsilon(p \bmod N)\cdot\bigl[\,p \mid n\,\bigr]\,a_{n/p} = a_p\,a_n,$$
--   where the indicator term is $a_{n/p}$ when $p \mid n$ and $0$ otherwise. The conclusion asserts the existence of a real constant $C$ such that for every real $s$ with $1 < s < 2$ the family $p \mapsto \|a_p\|^2 p^{-s}$, indexed by the subtype of natural numbers $p$ that are prime and do not divide $N$, is summable, and
--   $$\sum_{p \nmid N} \|a_p\|^2 p^{-s} \le \log\frac{1}{s-1} + C.$$
--
--   This is Rankin's second-moment estimate in the form of Proposition 5.1 of Deligne–Serre's work on modular forms of weight one, specialised to weight $k = 1$. It is the analytic input for the statements that the coefficients $a_p$ take finitely many values outside a set of primes of small upper density and, through these, for the construction of the complex Galois representation attached to a weight-one Hecke eigenform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → s < 2 →
      Summable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ N} =>
        ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) ∧
      ∑' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
          ‖ModularFormClass.qCoeff f (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
        Real.log (1 / (s - 1)) + C := by sorry
