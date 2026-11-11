-- Prove2me | Theorems.Thm_FTConnOracle_Main_observation_2_1
-- name    : FTConnOracle.Main.observation_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:28:35.493875+00:00
-- url     : https://prove2.me/theorems/6ee3aea9-850e-4323-af71-1231036873f3
-- title:
--   Observation 2.1 — an encoding admits an exact component decoder for at most f failures iff it is f-cut compatible
-- statement:
--   Let $n\ge2$, let $f\ge0$ be an integer, and let $\mathrm{Enc}$ be any map from the graphs on $[n]$ to any set. Then $\mathrm{Enc}$ admits an exact component decoder for failure of at most $f$ edges — some $\mathrm{Dec}$, seeing only $\mathrm{Enc}(G)$ and $F$, returns $\mathrm{cc}(G-F)$ for every graph $G$ on $[n]$ and every $F\subseteq E(G)$ with $|F|\le f$ — if and only if $\mathrm{Enc}$ is $f$-cut compatible:
--
--   $$\exists\,\mathrm{Dec}\ \forall G\ \forall F\subseteq E(G),\ |F|\le f:\ \mathrm{Dec}(\mathrm{Enc}(G),F)=\mathrm{cc}(G-F)\iff\mathrm{Enc}\text{ is }f\text{-cut compatible}.$$
--
--   The observation characterises the encodings that can serve as component oracles purely in terms of which graphs they identify; both constructions of §4 are certified through it.
--
--   **Formalization Note.** The component partition is the reachability relation of $G-F$ on $[n]$.
--
--   Differences from the source:
--   - encoding: an encoding admits an exact component decoder for failure of at most f edges → AdmitsDecoder Enc f: ∃ Dec : α → Finset (Sym2 (Fin n)) → (Fin n → Fin n → Prop) with Dec (Enc G) F = (G − F).Reachable for all G and all F ⊆ E(G) with |F| ≤ f; Enc any map into any type α; reason: the paper's notion (§2.1: correct on valid queries, unrestricted elsewhere); the component partition is the reachability relation
--   - generalization: an encoding of a graph to a bit string (§2), or Enc : I → [M] with finitely many states (§2.1) → Enc : SimpleGraph (Fin n) → α for an arbitrary type α; reason: the observation and its proof use only equality of encodings; bit strings and [M] are instances, so the statement specializes to the source's
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 6 (PDF 8), Observation 2.1

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle

namespace FTConnOracle.Main

/-- Observation 2.1 (p. 6): an encoding of the graphs on `[n]` admits an exact component decoder
for failure of at most `f` edges if and only if it is `f`-cut compatible. -/
theorem observation_2_1 {n : ℕ} (hn : 2 ≤ n) {α : Type} (Enc : SimpleGraph (Fin n) → α)
    (f : ℕ) :
    AdmitsDecoder Enc f ↔ IsCutCompatible Enc f := by sorry

end FTConnOracle.Main
