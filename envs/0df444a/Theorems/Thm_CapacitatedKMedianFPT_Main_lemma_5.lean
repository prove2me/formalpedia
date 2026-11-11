-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_lemma_5
-- name    : CapacitatedKMedianFPT.Main.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:49.865421+00:00
-- url     : https://prove2.me/theorems/2e368869-02fe-4824-80ae-594621d4c8f7
-- title:
--   Lemma 5 — the savings function v is monotone and submodular
-- statement:
--   In the setting of Lemma 3, fix quotas $q_{T,i}\in\mathbb N$ and let $v(S)$ be the maximum weight, under the weights $w=\tilde d-d$, of a quota-constrained matching using $S$. Then $v$ is a monotone submodular function on $\bigcup_iF_i$:
--   $$A\subseteq B\Rightarrow v(A)\le v(B),\qquad v(A)+v(B)\ge v(A\cup B)+v(A\cap B).$$
--
--   This lets the algorithm maximize the savings by the submodular maximization of Theorem 4.
--
--   **Formalization Note** $v(S)$ only uses facilities of $S\cap\bigcup_iF_i$, so the stated properties over all subsets of the point set are equivalent to the properties over subsets of $\bigcup_iF_i$.
--
--   Differences from the source:
--
--   - generalization: v defined with the guessed quotas ỹ_(T,i) → v defined with arbitrary quotas q_(T,i) ∈ ℕ; reason: the guessed values are particular quotas
--   - encoding: monotone submodular on ∪_i F_i → monotone and submodular on all subsets of the point set; reason: v(S) = v(S ∩ ∪_i F_i), so the two statements are equivalent
--   - generalization: the branch fixed by the enumeration: (ℓ, r̃) an entry of L, χ from an k-perfect family, h(c) = argmin with the source's ties → any leaders that are clients, any radii in ℕ, any coloring χ : P → [k], any permutation π and any nearest-leader choice h; reason: the statement uses only these properties; the source's branch is one instance
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 13, Lemma 5 and proof; p. 12, savings function

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Proxy
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Lemma 5** (p. 13). For every choice of quotas `ỹ`, the savings function `v` (maximum weight of
a quota-constrained matching using `S`) is monotone and submodular. Since `v(S)` only uses the
facilities of `S ∩ ⋃_i F_i`, this is the statement on subsets of `⋃_i F_i`. -/
theorem lemma_5 {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (G : Guess I)
    (q : ClientType I.k → Fin I.k → ℕ)
    (hI : I.IsValid) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hD : I.HasIntDistancesUpTo (distanceBound I.size ε))
    (hℓ : ∀ i, G.ℓ i ∈ I.C) (hh : G.IsNearestLeader) :
    SubsamplingSM.Offline.IsMonotoneSetFn (G.savings ε q) ∧
      NonmonotoneSubmod.Shared.Submodular (G.savings ε q) := by sorry

end CapacitatedKMedianFPT.Main
