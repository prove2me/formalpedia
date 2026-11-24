-- Prove2me | Theorems.Thm_DeepONetUniversal_arzela_ascoli
-- name    : DeepONetUniversal.arzela_ascoli
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:32:27.184614+00:00
-- url     : https://prove2.me/theorems/ebebb160-b0bd-4360-952b-1a0f64e4d6bd
-- title:
--   Theorem 6: Arzelà–Ascoli theorem
-- statement:
--   Let $X$ be a Banach space and $K\subset X$ compact. A subset $V$ of $C(K)$, with the sup norm $\|f\|_{C(K)}=\max_{x\in K}|f(x)|$, has compact closure if and only if
--
--   1. $V$ is uniformly bounded: there is $M$ with $|f(x)|\le M$ for all $f\in V$, $x\in K$; and
--   2. $V$ is equicontinuous: for every $\varepsilon>0$ there is $\delta>0$ such that $|f(x)-f(y)|<\varepsilon$ for all $f\in V$ and all $x,y\in K$ with $\|x-y\|<\delta$.
--
--   The paper uses it to describe the compact sets of input functions required by Theorems 4 and 5, and in the proof of Lemma 7.
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Appendix A, Theorem 6, with Definitions 3 and 4, pp. 19-20

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology

namespace DeepONetUniversal

theorem arzela_ascoli {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (K : Set X) (hK : IsCompact K) (V : Set C(K, ℝ)) :
    IsCompact (closure V) ↔
      IsUniformlyBounded ((fun f : C(K, ℝ) => (f : K → ℝ)) '' V) ∧
        IsEquicontinuousFamily ((fun f : C(K, ℝ) => (f : K → ℝ)) '' V) := by sorry

end DeepONetUniversal
