-- Prove2me | Theorems.Thm_EulerianLE_theorem_8
-- name    : EulerianLE.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:32.270431+00:00
-- url     : https://prove2.me/theorems/d3afdab9-3a95-4642-8fd1-3f1dc298c153
-- title:
--   Theorem 8 — composability from local conditions
-- statement:
--   Let $A$ be an algorithm that terminates on every input of a class $I$, and let $d\ge0$ be an integer. Suppose that for every input of $I$ and every node $u$, the program of $u$ satisfies, under every pattern of pulse deliveries to its ports:
--
--   1. when the program completes, $\sum_i\sigma_i[u]=\sum_i\rho_i[u]$;
--   2. for every port $i$, port $i$ has terminated if and only if $\sigma_i[u]+\rho_i[u]=d$;
--   3. the program eventually consumes every pulse that it observes.
--
--   Then $A$ is composable on $I$.
--
--   All three conditions concern a single node's program, so composability, a global property of all executions with all following algorithms, reduces to checks on each program. The conditions must hold for every delivery pattern, including patterns that no standalone execution of $A$ produces; App. B.1 of the paper shows that neither (2) nor (3) may be dropped or checked on standalone executions only.
--
--   Differences from the source:
--   - generalization: the paper's network: a finite connected undirected Eulerian graph → any port-numbered multigraph (`Network`), with no Eulerian or connectivity hypothesis; reason: the statement concerns arbitrary algorithms and does not use the Eulerian property; Eulerian networks are a special case
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: "for any arbitrary pattern of pulse deliveries"; "port i has terminated"; "eventually consumes every pulse that it observes" → over all local runs of the node's program (`LReach`, with deliveries gated like scheduler events); `PortTerminated` (no further operation on i under any continuation, App. C.1); `LocalCond3` (without further deliveries, every observed pulse is consumed); reason: the readings of App. C.1 (p.34) and Lemma 19 (3) ("even if there are none"); footnote 3, p.10, says the same of condition (3)
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §3.2, p.10 (PDF p.12), Theorem 8

import Mathlib
import Definitions.Def_EulerianLE_IsComposable
import Definitions.Def_EulerianLE_LReach

namespace EulerianLE

/-- **Theorem 8** (Composability from local conditions; Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §3.2, p.10,
PDF p.12). Let `A` be an algorithm that terminates on every input in a class `I`, and let `d ≥ 0` be an
integer. Suppose that, for every input in `I` and every node `u`, the following hold for the program of
`u`, for any arbitrary pattern of pulse deliveries to `u`'s ports. (1) When the program completes, it
holds `∑_i σ_i[u] = ∑_i ρ_i[u]`. (2) For every port `i ∈ [deg(u)]`, port `i` has terminated if and only if
`σ_i[u] + ρ_i[u] = d`. (3) The program eventually consumes every pulse that it observes. Then `A` is
composable on `I`.

**Formalization Note.** "For any arbitrary pattern of pulse deliveries" is over local runs of the
node's program (`LReach`), including patterns that no standalone execution produces (p.10; App. B.1
shows that standalone executions do not suffice). `d = 0` is allowed. Condition (3) is read with
Lemma 19's "even if there are none" (`LocalCond3`), and port termination as in App. C.1
(`PortTerminated`). -/
theorem theorem_8 {G : Network} {In O₁ : G.V → Type} (A : Algorithm G.V G.deg In O₁)
    (I : Set (∀ v, In v)) (hT : TerminatesOn A I) (d : ℕ)
    (h1 : ∀ x ∈ I, ∀ u, LocalCond1 (A u (x u)))
    (h2 : ∀ x ∈ I, ∀ u, LocalCond2 (A u (x u)) d)
    (h3 : ∀ x ∈ I, ∀ u, LocalCond3 (A u (x u))) : IsComposable A I := by sorry

end EulerianLE
