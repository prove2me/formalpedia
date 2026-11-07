-- Prove2me | Theorems.Thm_EulerianLE_lemma_4
-- name    : EulerianLE.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:02.339299+00:00
-- url     : https://prove2.me/theorems/c4ddcfe8-072c-4725-a81f-421fad18f21d
-- title:
--   Lemma 4 — splicing two pairs on distinct circuits merges them and preserves the CW orientation
-- statement:
--   Fix a port pairing $\pi[w]$ at every node $w$ and two stored pairs $(i,\bar\imath),(j,\bar\jmath)\in\pi[v]$ of a node $v$ that lie on distinct circuits $C_1\ni i$ and $C_2\ni j$. Let $\pi'$ be the pairings after the splice at $v$, which replaces the two pairs by $(i,\bar\jmath)$ and $(j,\bar\imath)$. Then:
--
--   1. two ports lie on the same circuit of $\pi'$ if and only if they lie on the same circuit of $\pi$ or both lie on $C_1\cup C_2$; so $C_1$ and $C_2$ merge into one circuit with edge set $E(C_1)\cup E(C_2)$ and the other circuits are unchanged;
--   2. if $C_1$ and $C_2$ are oriented with $\bar\imath$ and $\bar\jmath$ outgoing CW ports, the orientation of the new circuit in which $\bar\imath$ is outgoing has as its outgoing ports exactly the outgoing CW ports of $C_1$ and of $C_2$:
--   $$\mathrm{CW}_{\pi'}(\bar\imath)=\mathrm{CW}_{\pi}(\bar\imath)\cup\mathrm{CW}_{\pi}(\bar\jmath).$$
--
--   Splicing is how the algorithm merges circuits while keeping their orientations, in Program 4 and in Program 6.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: circuits with edge sets; an orientation of a circuit → classes of the relation `SameCircuit` on ports; the set `cwOrbit` of outgoing ports of a traversal; reason: an edge's two ports always lie in one class, so a class determines the edge set, and the outgoing ports determine the traversal direction
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.7 (PDF p.9), Lemma 4

import Mathlib
import Definitions.Def_EulerianLE_SameCircuit

namespace EulerianLE

/-- **Lemma 4** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.7, PDF p.9). Let `(i, ī), (j, j̄) ∈ π` be two
port pairs of some node that lie on distinct circuits `C₁` and `C₂`. Then splicing these two pairs
merges `C₁` and `C₂` into a single circuit with edge set `E(C₁) ∪ E(C₂)` and leaves all other circuits
unchanged. If `C₁` and `C₂` are oriented and `ī` and `j̄` are outgoing CW ports, then the new circuit is
oriented and its orientation traverses the edges of `C₁` and of `C₂` in their CW directions.

**Formalization Note.** `a = (i, ī)` and `b = (j, j̄)` are stored pairs of the pairing at `v`; the splice
`splice` replaces them by `(i, j̄)` and `(j, ī)`. Circuits are classes of `SameCircuit`; the first
conjunct says that the classes after the splice are the union of the classes of `(v, i)` and `(v, j)`
and the other classes unchanged (an edge set is determined by its class). The CW orientation of `C₁`
with `ī` outgoing is the set `cwOrbit pp (v, ī)` of its outgoing CW ports, and similarly for `C₂`; the
second conjunct says that the orientation of the new circuit in which `ī` is outgoing has exactly the
outgoing CW ports of `C₁` and of `C₂`. -/
theorem lemma_4 (G : Network) (pp : ∀ v, Pairs (G.deg v)) (hpp : ∀ v, IsPairing (pp v)) (v : G.V)
    (a b : Fin (G.deg v) × Fin (G.deg v)) (ha : a ∈ pp v) (hb : b ∈ pp v)
    (hdist : ¬ SameCircuit pp ⟨v, a.1⟩ ⟨v, b.1⟩) :
    (∀ p q, SameCircuit (Function.update pp v (splice (pp v) a b)) p q ↔
        (SameCircuit pp p q ∨
          ((SameCircuit pp p ⟨v, a.1⟩ ∨ SameCircuit pp p ⟨v, b.1⟩) ∧
            (SameCircuit pp q ⟨v, a.1⟩ ∨ SameCircuit pp q ⟨v, b.1⟩)))) ∧
    cwOrbit (Function.update pp v (splice (pp v) a b)) ⟨v, a.2⟩ =
      cwOrbit pp ⟨v, a.2⟩ ∪ cwOrbit pp ⟨v, b.2⟩ := by sorry

end EulerianLE
