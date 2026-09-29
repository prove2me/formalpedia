-- Prove2me | Theorems.Thm_DistInterpRO_Equivalence_nested_dual_solution
-- name    : DistInterpRO.Equivalence.nested_dual_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:45:25.737221+00:00
-- url     : https://prove2.me/theorems/d75b4115-1fa2-4f2b-9496-61ccc92d9b03
-- title:
--   The nested dual solution $\alpha_{\{1,\dots,i\}}=f_i-f_{i+1}$, $\alpha_N=f_n$ is feasible and attains $\sum_i c_if_i$
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ be measurable, let $c_1,\dots,c_n>0$ with $\sum_i c_i=1$, and let $\mathcal Z_1,\dots,\mathcal Z_n\subseteq\mathbb R^m$ be nonempty Borel sets on each of which $f$ is bounded below. Put $f_i=\inf_{x\in\mathcal Z_i}f(x)$ and assume the sets are ordered so that
--   $$f_1\ge f_2\ge\dots\ge f_n.$$
--   Let $\alpha$ be the nested dual solution: $\alpha_S=0$ except $\alpha_{\{1,\dots,i\}}=f_i-f_{i+1}$ for $i<n$ and $\alpha_N=f_n$. Then
--
--   1. $\alpha$ is dual feasible: $\sum_S\alpha_S\mathbf 1(x\in\mathcal Z_S)\le f(x)$ for all $x\in\mathcal Z_N$ and $\alpha_S\ge0$ for all $S\ne N$;
--   2. for each $i$, $\sum_{S\subseteq N}\alpha_S\,\mathbf 1(i\in S)=f_i$;
--   3. its objective value is $\sum_{i\in N}c_i\sum_{S\subseteq N}\alpha_S\mathbf 1(i\in S)=\sum_{i\in N}c_if_i$.
--
--   Together with the dual bound, this shows that the dual optimum equals $\sum_i c_i f_i$.
--
--   **Formalization Note** The ordering $f_1\ge\dots\ge f_n$ is the proof's "without loss of generality" and appears only here, not in Theorem 2.1. Indices are `Fin n` and $\{1,\dots,i\}$ is `Finset.Iic i`. The paper checks $\alpha_S\ge0$ for all $S$ (it has shifted $f$ so that $f\ge 1$); the dual problem only requires it for $S\ne N$, and that is what is stated, without the shift.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 97, proof of Theorem 2.1, from 'To show the reverse inequality' to the end of the proof

import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem nested_dual_solution {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (hsorted : Antitone (fun i : Fin n => ⨅ x : Z i, f x)) :
    IsDualFeasible Z f (nestedDual (fun i => ⨅ x : Z i, f x)) ∧
      (∀ i : Fin n, ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
            ⨅ x : Z i, f x) ∧
      ∑ i, c i * ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
        ∑ i, c i * ⨅ x : Z i, f x := by sorry

end DistInterpRO.Equivalence
