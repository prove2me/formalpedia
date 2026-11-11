-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_claim_2
-- name    : CapacitatedKMedianFPT.Main.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:31.772693+00:00
-- url     : https://prove2.me/theorems/a21989d2-b12c-4a9d-81ea-6050809c1d09
-- title:
--   Claim 2 — every count-matching assignment has proxy cost exactly Z
-- statement:
--   In the setting of Lemma 4, an assignment $\varphi'$ of the clients to $\bigcup_iF_i$ is count-matching if, for every type $T$ and every $i\in[k]$, exactly $y_{T,i}$ clients of type $T$ are sent into $F_i$. Every count-matching assignment $\varphi'$ satisfies
--   $$\sum_{c\in C}\tilde d(c,\varphi'(c))=Z.$$
--
--   The assignment need not respect capacities and may use several facilities of a group. The claim lets one replace the optimal assignment by any assignment with the same type counts at no proxy cost.
--
--   Differences from the source:
--
--   - generalization: the branch fixed by the enumeration: (ℓ, r̃) an entry of L, χ from an k-perfect family, h(c) = argmin with the source's ties → any leaders that are clients, any radii in ℕ, any coloring χ : P → [k], any permutation π and any nearest-leader choice h; reason: the statement uses only these properties; the source's branch is one instance
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 11, count-matching, proxy assignment cost and Claim 2

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Proxy

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

/-- **Claim 2** (p. 11). In the branch of Lemma 2 with `o⋆_i ∈ F_i` for every `i`, every
count-matching assignment `φ'` has proxy assignment cost `∑_c d̃(c, φ'(c))` exactly `Z`. -/
theorem claim_2 {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (G : Guess I)
    (o : Fin I.k → P) (φs : P → P)
    (hI : I.IsValid) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hD : I.HasIntDistancesUpTo (distanceBound I.size ε))
    (hℓ : ∀ i, G.ℓ i ∈ I.C) (hh : G.IsNearestLeader)
    (hopt : I.IsIndexedOptimum o φs) (hn : ∀ i, 1 ≤ I.load φs (o i))
    (h32 : ∑ i, (I.load φs (o i) : ℝ) * I.d (o i) (G.ℓ i) ≤ (1 + 2 * ε) * I.cost φs)
    (h33 : ∑ i, (I.load φs (o i) : ℝ) * (G.r i : ℝ) ≤ (1 + 5 * ε) * I.cost φs)
    (hgrp : ∀ i, o i ∈ G.group i)
    (φ' : P → P) (hφ' : G.IsCountMatching ε o φs φ') :
    ∑ c ∈ I.C, G.proxyDist ε c (φ' c) = G.proxyOpt ε φs := by sorry

end CapacitatedKMedianFPT.Main
