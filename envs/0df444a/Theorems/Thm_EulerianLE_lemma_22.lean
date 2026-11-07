-- Prove2me | Theorems.Thm_EulerianLE_lemma_22
-- name    : EulerianLE.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:51.947995+00:00
-- url     : https://prove2.me/theorems/925841ee-3112-40ef-b3fb-94651d2732a2
-- title:
--   Lemma 22 — on a relay trail pulses only travel between the endpoints; a trail acts as an edge
-- statement:
--   Consider an execution of round $L_r$ ($r\ge1$) from a valid round-$r$ configuration, and the relay trail from a port $p$ of a non-relay node to its successor $q$, with relay pairs $(q_h,\bar q_h)$ entered at $q_h$ from the side of $p$.
--
--   1. (a) At every time at which at most two pulses have been sent through each of $p$ and $q$, every relay pair has sent through $\bar q_h$ at most as many pulses as it consumed at $q_h$ and through $q_h$ at most as many as it consumed at $\bar q_h$ (every send forwards a pulse away from the endpoint it came from), and the pulses delivered at each endpoint are at most those sent through the other.
--   2. (b) If each endpoint sends at most two pulses during the round, the trail acts as an edge.
--   3. (b) If moreover each endpoint sends exactly two, every relay pair eventually has consumed and sent exactly two pulses at each of its ports (it forwards two pulses in each direction) and its OR instance returns $(1,\text{non-witness})$ at Line 15 of Program 6.
--
--   Relay trails carry the pulses between non-relay nodes; this lemma is what lets the round analysis treat them as edges.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: the standing assumptions of §C.2: r ≥ 1, a valid round-r configuration I, an arbitrary standalone execution of L_r on I → hypotheses `1 ≤ r`, `ValidConfig G ids r x`, a fair run `ρ` of `roundAlg G ids r` on `x`, an Eulerian network and injective identifiers; reason: these are the section's standing assumptions (p.36), stated as binders
--   - reading: "every send so far by a relay pair forwards a pulse away from the endpoint it comes from"; "every pulse delivered at an endpoint comes from the other endpoint"; "acts as an edge" → count form: sends through each side of a relay pair are at most the consumptions at the other side; deliveries at an endpoint are at most, and eventually at least, the sends through the other (`ForwardsAway`, `ActsAsEdge`); reason: pulses are indistinguishable and channels FIFO (p.8), and the sent pulse is regarded as the consumed one (p.8), so these counts are the printed claims
--   - encoding: "returns (1, non-witness) in Line 15 of Program 6" → the pair's OR output, recorded in the variable `qout` at its two ports, is (1, non-witness) at some time; reason: the variable is written once per round, when the instance returns
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.2, p.37 (PDF p.39), Lemma 22

import Mathlib
import Definitions.Def_EulerianLE_relayTrail

namespace EulerianLE

/-- **Lemma 22** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. C.2, p.37, PDF p.39). Consider a relay trail.
(a) At every time at which at most two pulses have been sent through each endpoint, every send so far
by a relay pair on the trail forwards a pulse away from the endpoint it comes from; in particular,
every pulse delivered at an endpoint comes from the other endpoint.
(b) If each endpoint sends at most two pulses into the trail during the round, the trail acts as an
edge. If each sends exactly two, every relay pair on it also forwards two pulses in each direction and
returns `(1, non-witness)` in Line 15 of Program 6.

**Formalization Note.** As in §C.2 (p.36), `r ≥ 1`, `x` is a valid round-`r` configuration on the
Eulerian network `G` with distinct identifiers, and `ρ` is an arbitrary standalone execution (fair run) of
`L_r` on `x`. Relay trails and successors refer to the input pairing `π⊤ = pairsOf G x`. The trail runs from the port `p` of a
non-relay node to its successor `q`; `ys` are the ports `q_h` at which it enters its relay pairs
`(q_h, q̄_h)`. The claims are in count form (`ForwardsAway`, `ActsAsEdge`): pulses are indistinguishable
and channels FIFO, so these counts are the printed claims. "Forwards two pulses in each direction" is:
from some time on, each port of the pair has consumed exactly two pulses and sent exactly two; "returns
`(1, non-witness)`" is: the pair's OR output `qout`, recorded at its two ports when the instance returns,
is `(1, non-witness)` at some time. -/
theorem lemma_22 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ) (hid : Function.Injective ids)
    (r : ℕ) (hr : 1 ≤ r) (x : ∀ u, CIO G u) (hx : ValidConfig G ids r x)
    (ρ : Run ((roundAlg G ids r).progs x) (stdTag _)) (hρ : IsFair ρ)
    (p q : G.Port) (hp : NonRelay G ids r p.1)
    (hq : succPort ids r (pairsOf G x) p = some q) :
    (∀ t, (ρ.cfg t).sent p ≤ 2 → (ρ.cfg t).sent q ≤ 2 →
      ForwardsAway ρ (pairsOf G x) (relayTrail ids r (pairsOf G x) p).1 t ∧
      (ρ.cfg t).delivered q ≤ (ρ.cfg t).sent p ∧ (ρ.cfg t).delivered p ≤ (ρ.cfg t).sent q) ∧
    ((∀ t, (ρ.cfg t).sent p ≤ 2 ∧ (ρ.cfg t).sent q ≤ 2) →
      ActsAsEdge ρ (pairsOf G x) p q (relayTrail ids r (pairsOf G x) p).1) ∧
    ((∀ t, (ρ.cfg t).sent p ≤ 2 ∧ (ρ.cfg t).sent q ≤ 2) →
      (∃ t, (ρ.cfg t).sent p = 2 ∧ (ρ.cfg t).sent q = 2) →
      ∀ y ∈ (relayTrail ids r (pairsOf G x) p).1,
        (∃ t, ∀ t', t ≤ t' →
          (ρ.cfg t').consumed y = 2 ∧ (ρ.cfg t').sent (partner (pairsOf G x) y) = 2 ∧
          (ρ.cfg t').consumed (partner (pairsOf G x) y) = 2 ∧ (ρ.cfg t').sent y = 2) ∧
        ∃ t st, roundStoreAt ρ y.1 t = some st ∧ st.qout y.2 = some (.one false)) := by sorry

end EulerianLE
