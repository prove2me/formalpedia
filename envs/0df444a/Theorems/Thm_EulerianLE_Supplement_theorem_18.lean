-- Prove2me | Theorems.Thm_EulerianLE_Supplement_theorem_18
-- name    : EulerianLE.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:18:47.743316+00:00
-- url     : https://prove2.me/theorems/2d1cb5c4-c622-4b5d-b67e-4f56ee074982
-- title:
--   Theorem 18 — every content-oblivious leader-election algorithm sends $\Omega(|E|\log \mathrm{ID}_{\max})$ pulses on every 2-edge-connected network
-- statement:
--   Fix a 2-edge-connected network $G=(V,E)$. Any content-oblivious leader election algorithm sends $\Omega(|E|\log \mathrm{ID}_{\max})$ pulses on $G$ in the worst case.
--
--   Precisely: there is an absolute constant $c>0$ such that for every simple 2-edge-connected network $G$ there is a threshold $N$, depending on $G$ only, with the following property. For every $\mathrm{ID}_{\max}\ge N$ and every leader-election algorithm $A$ for identifiers in $[\mathrm{ID}_{\max}]=\{1,\dots,\mathrm{ID}_{\max}\}$, there are an assignment of distinct identifiers from $[\mathrm{ID}_{\max}]$ to the nodes of $G$ and a standalone execution of $A$ on $G$ in which, by some time,
--
--   $$\#\{\text{pulses sent}\}\ \ge\ c\cdot|E|\cdot\log_2 \mathrm{ID}_{\max}.$$
--
--   This shows that the pulse complexity of content-oblivious leader election must grow with the number of edges, not only with the number of nodes; on rings ($|E|=n$) it recovers the earlier $\Omega(n\log \mathrm{ID}_{\max})$ bound.
--
--   **Formalization Note** "In the worst case" is the maximum over identifier assignments and executions, hence the existentials over `ids` and the fair run. The algorithm $A$ is chosen after $\mathrm{ID}_{\max}$ and must be correct on every simple 2-edge-connected network with distinct identifiers from $[\mathrm{ID}_{\max}]$, not only on $G$, since the argument runs it on networks glued from two copies of $G$.
--
--   Differences from the source:
--   - encoding: networks are graphs G = (V, E) with port numbers → the mission's port-numbered Network restricted by IsSimpleNet (no self-loops, no parallel edges), every port numbering; reason: same instances
--   - generalization: any content-oblivious leader election algorithm → every family A id deg of node programs, possibly depending on IDmax, that is a leader-election algorithm for identifiers in [IDmax] on every simple 2-edge-connected network (a fair run exists; every fair run: all nodes complete, exactly one leader); reason: the proof fixes IDmax and then A, and uses only correctness on 2-edge-connected networks; uniform algorithms are the families not depending on IDmax, so the statement specializes to them
--   - reading: Ω(|E| log IDmax) pulses on G in the worst case → ∃ c > 0 absolute, ∀ simple 2-edge-connected G, ∃ N (depending on G only), ∀ IDmax ≥ N, ∀ A, ∃ distinct ids in [IDmax], ∃ fair run, ∃ t, c·|E|·log₂ IDmax ≤ pulses sent by t; reason: the asymptotic is in IDmax with a constant uniform in G and A, and the worst case maximizes over identifiers and executions
--   - reading: IDmax the largest identifier → IDmax the bound of the identifier range [IDmax]; reason: §6 and Theorem 2 draw identifiers from [IDmax]; the largest identifier used is at most IDmax
--   - reading: a 2-edge-connected graph → nonempty, connected, connected after deleting any one edge; the one-node network without edges included; reason: standard meaning; the one-node network has |E| = 0, and degree-0 programs are never run on the other networks of the class, so requiring correctness there excludes no algorithm
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), Theorem 18, p.28 (PDF p.30); proof pp.28–29 (PDF pp.30–31); informal form Theorem 2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_EulerianLE_Supplement_IsLEAlgorithm

namespace EulerianLE.Supplement

/-- **Theorem 18** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on
Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §6, p.28, PDF p.30; the formal
form of Theorem 2, p.3). Fix a 2-edge-connected network `G = (V, E)`. Any content-oblivious leader
election algorithm sends `Ω(|E| log IDmax)` pulses on `G` in the worst case.

There is an absolute constant `c > 0` such that for every simple 2-edge-connected network `G` there
is a threshold `N` (depending on `G` only) such that for every `IDmax ≥ N` and every leader-election
algorithm `A` for identifiers in `[IDmax]`, some assignment of distinct identifiers from `[IDmax]` to
the nodes of `G` and some standalone execution (fair run) of `A` on it send at least
`c · |E| · log₂ IDmax` pulses by some time.

**Formalization Note.** "In the worst case" is the maximum over identifier assignments and executions,
hence the two existentials. `c` is chosen before `G` and `A`; `N` before `A`. `A` is quantified after
`IDmax` (the proof fixes `IDmax` first), so it may depend on `IDmax`; it must be correct on every
simple 2-edge-connected network with distinct identifiers from `[IDmax]` (`IsLEAlgorithm`), as the
proof runs it on networks glued from two copies of `G`. Pulses are counted when sent (`totalSent`). -/
theorem theorem_18 :
    ∃ c : ℝ, 0 < c ∧ ∀ G : Network, IsSimpleNet G → IsTwoEdgeConnected G →
      ∃ N : ℕ, ∀ K : ℕ, N ≤ K → ∀ A : ℕ → (d : ℕ) → NodeProg d Outcome, IsLEAlgorithm K A →
        ∃ ids : G.V → ℕ, Function.Injective ids ∧ (∀ v, ids v ∈ Finset.Icc 1 K) ∧
          ∃ ρ : Run (fun v => A (ids v) (G.deg v)) (stdTag _), IsFair ρ ∧
            ∃ t, c * (G.edgeCount : ℝ) * Real.logb 2 K ≤ (ρ.totalSent t : ℝ) := by sorry

end EulerianLE.Supplement
