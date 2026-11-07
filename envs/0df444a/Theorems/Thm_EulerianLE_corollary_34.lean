-- Prove2me | Theorems.Thm_EulerianLE_corollary_34
-- name    : EulerianLE.corollary_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:35.954264+00:00
-- url     : https://prove2.me/theorems/404f52ca-200b-4c88-b3e6-b7d737a1baae
-- title:
--   Corollary 34 — a local leader without Counting nodes is elected and completes last
-- statement:
--   Consider an execution of round $L_r$ ($r\ge1$) from a valid round-$r$ configuration in which the Check node $\ell$ is a local leader and no node is Counting. Then every node completes $L_r$; the output is a successful configuration whose leader is $\ell$; every other node completes strictly before $\ell$; and every virtual node of the OR protocol on $C_\ell$ returns $0$: the OR instance of every port pair of $\ell$ and of every relay pair on a trail from a port of $\ell$.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: the standing assumptions of §C.2: r ≥ 1, a valid round-r configuration I, an arbitrary standalone execution of L_r on I → hypotheses `1 ≤ r`, `ValidConfig G ids r x`, a fair run `ρ` of `roundAlg G ids r` on `x`, an Eulerian network and injective identifiers; reason: these are the section's standing assumptions (p.36), stated as binders
--   - encoding: "every virtual node of the OR protocol on C_ℓ returns 0" → for every port of ℓ, and for every relay pair on the trail from a port of ℓ, the OR output recorded in `qout` at its ports is 0 at some time; reason: C_ℓ contains every port of ℓ (all circuits through ℓ are merged) and its relay pairs are the ℓ-pairs
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.5.1, p.44 (PDF p.46), Corollary 34

import Mathlib
import Definitions.Def_EulerianLE_relayTrail

namespace EulerianLE

/-- **Corollary 34** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. C.5.1, p.44, PDF p.46). Suppose that the
Check node `ℓ` is a local leader and no node is Counting. Then every node completes `L_r`, the output is
a successful configuration whose leader is `ℓ`, and `ℓ` completes the round after every other node.
Moreover, every virtual node of the OR protocol on `C_ℓ` returns `0`.

**Formalization Note.** As in §C.2 (p.36), `r ≥ 1`, `x` is a valid round-`r` configuration on the
Eulerian network `G` with distinct identifiers, and `ρ` is an arbitrary standalone execution (fair run) of
`L_r` on `x`. Relay trails and successors refer to the input pairing `π⊤ = pairsOf G x`. "No node is Counting": every identifier is
less than `r`. "`ℓ` completes after every other node": strictly earlier completion steps. The virtual nodes
of the OR protocol on `C_ℓ` are the OR instances of the port pairs of `ℓ` (all ports of `ℓ` lie on `C_ℓ`) and
those of the ℓ-pairs, the relay pairs on the trails from the ports of `ℓ`; "returns 0" is: the OR output
`qout` recorded at the pair's ports is `0` at some time. -/
theorem corollary_34 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ) (hid : Function.Injective ids)
    (r : ℕ) (hr : 1 ≤ r) (x : ∀ u, CIO G u) (hx : ValidConfig G ids r x)
    (ρ : Run ((roundAlg G ids r).progs x) (stdTag _)) (hρ : IsFair ρ)
    (ℓ : G.V) (hℓ : IsLocalLeader ids r (pairsOf G x) ℓ) (hnc : ∀ u, ids u < r) :
    ∃ y, ρ.Outputs y ∧ SuccessfulWith G y ℓ ∧
      (∀ w, w ≠ ℓ → ∀ tw tℓ, ρ.CompletesAt w tw → ρ.CompletesAt ℓ tℓ → tw < tℓ) ∧
      (∀ i : Fin (G.deg ℓ), ∃ t st, roundStoreAt ρ ℓ t = some st ∧ st.qout i = some .zero) ∧
      (∀ i : Fin (G.deg ℓ), ∀ y ∈ (relayTrail ids r (pairsOf G x) ⟨ℓ, i⟩).1,
        ∃ t st, roundStoreAt ρ y.1 t = some st ∧ st.qout y.2 = some .zero) := by sorry

end EulerianLE
