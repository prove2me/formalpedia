-- Prove2me | Theorems.Thm_ClusterDecomp_eq_2
-- name    : ClusterDecomp.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:19.389207+00:00
-- url     : https://prove2.me/theorems/5e6570b4-1688-4dc5-9905-d5483bf1b192
-- title:
--   (2), p.10 — the capacity of an $s,t$-cut of $H_A$
-- statement:
--   Let $(S,T)$ be an $s,t$-cut of the auxiliary graph $H_A$ of Algorithm 1 and $B=T\setminus\{t\}$. Then its capacity is
--   $$c_{s,t}(B)=w(B,V\setminus B)+\beta\,\mathrm{vol}(A\setminus B).$$
--
--   The first term measures the boundary of the retained set and the second penalizes the discarded volume. In particular, the cut $S=\{s\}$ has $B=A$ and capacity $w(A,V\setminus A)$.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights, with no positive-degree assumption; reason: the argument uses neither integrality, the ratio nor positive degrees; the graphs of the paper are instances
--   - generalization: β = (1 + ε/10)p → any real β; reason: the identity holds for every β; the printed β is an instance
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), (2), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Display (2).**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), (2), p.10 (PDF p.12).

"Note that for any s, t-cut (S, T) of HA, with s ∈ S, t ∈ T, and B = T ∖ {t}, its capacity is
c_{s,t}(B) ≜ w(B, V ∖ B) + β vol(A ∖ B)."

An exact equality for every `s,t`-cut of `H_A`. In particular `S = {s}` has `B = A` and capacity `w(A, V ∖ A)`. -/
theorem eq_2 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) (A : Finset V) (β : ℝ)
    (S : Finset (↥A ⊕ Bool)) (hs : srcA A ∈ S) (ht : snkA A ∉ S) :
    cutCap (HAcap G A β) S Sᶜ =
      G.cut (backboneOf A S) (backboneOf A S)ᶜ + β * G.vol (A \ backboneOf A S) := by sorry

end ClusterDecomp
