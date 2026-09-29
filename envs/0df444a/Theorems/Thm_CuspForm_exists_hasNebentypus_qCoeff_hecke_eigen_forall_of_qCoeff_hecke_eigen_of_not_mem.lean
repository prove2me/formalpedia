-- Prove2me | Theorems.Thm_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
-- name    : CuspForm.exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/61296176-5a86-5f6e-abff-b3c32f5936ab
-- title:
--   Refining a partial Hecke eigenform to a full eigenform
-- statement:
--   Let $M$ be a non-zero natural number, $k$ an integer, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and $S$ an arbitrary set of natural numbers. Let $f$ be a cusp form of weight $k$ for $\Gamma_1(M)$ with $f \neq 0$ which has nebentypus $\varepsilon$, i.e. for every $\gamma \in \Gamma_0(M) \subseteq \mathrm{SL}_2(\mathbb{Z})$ and every $\tau$ in the upper half-plane, $f(\gamma \cdot \tau) = \varepsilon(\gamma_{11})\,(\gamma_{10}\tau + \gamma_{11})^k f(\tau)$. Let $a : \mathbb{N} \to \mathbb{C}$ be such that for every prime $p$ with $p \notin S$ and $p \nmid M$, and every $n \in \mathbb{N}$,
--   $$a_{pn}(f) + \varepsilon(p)\,p^{k-1}\,[\,p \mid n\,]\,a_{n/p}(f) = a(p)\,a_n(f),$$
--   where $a_n(\cdot)$ denotes the $n$-th coefficient of the $q$-expansion of width $1$. Then there exist a cusp form $g \neq 0$ of weight $k$ for $\Gamma_1(M)$ with the same nebentypus $\varepsilon$, and a function $b : \mathbb{N} \to \mathbb{C}$, such that $b(p) = a(p)$ for all primes $p \notin S$ with $p \nmid M$; the displayed relation holds for $g$ and $b$ at every prime $p \nmid M$ (not merely those outside $S$) and every $n$; and $a_{qn}(g) = b(q)\,a_n(g)$ for every prime $q \mid M$ and every $n$.
--
--   This is the passage from a cusp form that is an eigenvector of the Hecke operators $T_p$ for the primes $p \nmid M$ outside a set $S$ to a simultaneous eigenform for all $T_p$ with $p \nmid M$ and all $U_q$ with $q \mid M$, inside the nebentypus component $S_k(M,\varepsilon)$, with the eigenvalues unchanged away from $S$. It supplies the cusp-form side of the eigenclass formulation of the Eichler–Shimura correspondence, and is used by [`CohCarrier.exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul`](thm.html#CohCarrier.exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem.lean

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (S : Set ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hf0 : f ≠ 0) (hε : CuspForm.HasNebentypus ε f)
    (a : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff f (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
        a p * ModularFormClass.qCoeff f n) :
    ∃ (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (b : ℕ → ℂ),
      g ≠ 0 ∧ CuspForm.HasNebentypus ε g ∧
      (∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → b p = a p) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n) ∧
      (∀ q : ℕ, q.Prime → q ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) := by sorry
