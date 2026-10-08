-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_reverse_eq_forward
-- name    : ConservativeAD.AutoDiff.reverse_eq_forward
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:38.354879+00:00
-- url     : https://prove2.me/theorems/8f1279c0-8ec7-416a-9139-3f1298e9901d
-- title:
--   Proof of Theorem 8 — reverse mode (Algorithm 3) computes the same output as forward mode (Algorithm 2)
-- statement:
--   Fix an evaluation program and any family of vectors $d_k\in\mathbb R^{|\mathtt{parents}(k)|}$. Run Algorithm 3 with these $d_k$: start from $v=(0,\dots,0,1)\in\mathbb R^q$ and, for $t=q,\dots,p+1$ and every $j\in\mathtt{parents}(t)$, update $v[j]:=v[j]+v[t]\,d_{tj}$. After step $t$,
--
--   $$
--   v_t=(I+\tilde d_te_t^T)\cdots(I+\tilde d_qe_q^T)\,e_q ,
--   $$
--
--   and the output $(v[1],\dots,v[p])$ equals the output $\partial x_q/\partial x_{1,\dots,p}$ of Algorithm 2 for the same $d_k$.
--
--   Consequently the reverse-mode field $D_{\mathrm{rev}}$ and the forward-mode field $D_{\mathrm{fwd}}$ coincide, which gives part (ii) of Theorem 8 from part (i).
--
--   **Formalization Note** Algorithm 3 is implemented with the accumulating update $v[j]:=v[j]+v[t]d_{tj}$, which the proof's formula for $v_t$ computes; the printed "$v[j]:=v[t]d_{tj}$" would make this statement false whenever a node has two children. The equality is stated for every family $d$.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 23, §5.2, proof of Theorem 8 (reverse mode)

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_Program

namespace ConservativeAD.AutoDiff

/-- Proof of Theorem 8, p. 23: for every family `d` of vectors `d_k`, the output of Algorithm 3
(reverse mode, with the accumulating update `v[j] := v[j] + v[t] d_{tj}`) equals the output of
Algorithm 2 (forward mode). -/
theorem reverse_eq_forward {p q : ℕ} (P : Program p q) (d : P.Choice) :
    P.reverse d = P.forward d := by sorry

end ConservativeAD.AutoDiff
