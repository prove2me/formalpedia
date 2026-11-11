-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_claim_3
-- name    : CapacitatedKMedianFPT.Main.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:52.300513+00:00
-- url     : https://prove2.me/theorems/dbe58e45-58e9-4664-a001-82f78d411cbf
-- title:
--   Claim 3 — v(O⋆) ≥ Z − OPT
-- statement:
--   In the setting of Lemma 4, with the quotas $\tilde y_{T,i}=\mu_\varepsilon(y_{T,i})$ of the correct guess, the savings of the optimal facilities satisfy
--   $$v(O^\star)\ge Z-\mathrm{OPT}.$$
--
--   Together with Theorem 4 and Lemma 4 this gives the factor $1+2/e$.
--
--   Differences from the source:
--
--   - generalization: the branch fixed by the enumeration: (ℓ, r̃) an entry of L, χ from an k-perfect family, h(c) = argmin with the source's ties → any leaders that are clients, any radii in ℕ, any coloring χ : P → [k], any permutation π and any nearest-leader choice h; reason: the statement uses only these properties; the source's branch is one instance
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 14, Claim 3 and proof; p. 11–12, upper quota ỹ_(T,i) = μ_ε(y_(T,i))

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Proxy

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

/-- **Claim 3** (p. 14). In the branch of Lemma 2 with `o⋆_i ∈ F_i` for every `i` and quotas
`ỹ_{T,i} = μ_ε(y_{T,i})`, the savings of the optimal facilities satisfy `v(O⋆) ≥ Z − OPT`. -/
theorem claim_3 {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (G : Guess I)
    (o : Fin I.k → P) (φs : P → P)
    (hI : I.IsValid) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hD : I.HasIntDistancesUpTo (distanceBound I.size ε))
    (hℓ : ∀ i, G.ℓ i ∈ I.C) (hh : G.IsNearestLeader)
    (hopt : I.IsIndexedOptimum o φs) (hn : ∀ i, 1 ≤ I.load φs (o i))
    (h32 : ∑ i, (I.load φs (o i) : ℝ) * I.d (o i) (G.ℓ i) ≤ (1 + 2 * ε) * I.cost φs)
    (h33 : ∑ i, (I.load φs (o i) : ℝ) * (G.r i : ℝ) ≤ (1 + 5 * ε) * I.cost φs)
    (hgrp : ∀ i, o i ∈ G.group i) :
    G.proxyOpt ε φs - I.cost φs ≤
      G.savings ε (G.roundedQuota ε o φs) (Finset.univ.image o) := by sorry

end CapacitatedKMedianFPT.Main
