-- Prove2me | Theorems.Thm_BunkbedAux_wzGraph_abc_eq_alt
-- name    : BunkbedAux.wzGraph_abc_eq_alt
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T00:45:08.511004+00:00
-- url     : https://prove2.me/theorems/1b1de26f-061c-4760-b0f4-9967a9754014
-- title:
--   The alternative model is a slice of the Wierman--Ziff model
-- statement:
--   The Wierman--Ziff model and the *alternative* bunkbed hypergraph percolation model look rather different at first sight. In the WZ model each hyperedge independently takes one of five states **on each of the two levels**, the state recording which of its three vertices it connects. In the alternative model there is a single random choice per hyperedge — a level $\sigma(i) \in \{0,1\}$ — and the hyperedge contributes a complete triangle on that level and nothing at all on the other.
--
--   This lemma identifies the alternative model as a slice of the WZ model. Consider the WZ configuration which, for each hyperedge $i$, assigns
--   $$\psi(i, \sigma(i)) = abc \qquad\text{and}\qquad \psi(i, 1 - \sigma(i)) = a|b|c,$$
--   that is, the fully connecting state on level $\sigma(i)$ and the fully disconnecting state on the other level. Then the graph it realises on the bunkbed is **exactly** the alternative-model graph at level assignment $\sigma$:
--
--   $$\mathrm{wzGraph}\bigl(\text{triples},\, T,\, \psi\bigr) \;=\; \mathrm{altBBGraph}\bigl(\text{edges},\, T,\, \sigma\bigr).$$
--
--   The content is that the state $abc$ on a hyperedge with three distinct vertices contributes precisely the triangle on those vertices, which is the clique the alternative model places there, while the state $a|b|c$ contributes no edges at all; the vertical posts over the transversal set $T$ are present in both models by definition.
--
--   **Mathematical role.** This is the link between Section 3's robustness lemma and Hollom's original hypergraph counterexample. In the proof of the robustness lemma one conditions on the event that every hyperedge is fully present on one level and fully absent on the other; this lemma says that, conditioned on that event, the WZ model *is* the alternative model, so Hollom's computation of $12/64$ and $13/64$ can be quoted directly. It is also the reason the leading coefficient of the difference polynomial equals $13 - 12 = 1$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.6 (p. 6): 'Conditioning on A effectively transforms the WZ model into the alternative bunkbed hypergraph percolation model', used there to invoke Lemma 3.1.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **The alternative model sits inside the Wierman-Ziff model.** Take the WZ configuration on
Hollom's hypergraph that puts the *full* triangle on level `σ i` of hyperedge `i` (state `abc`)
and *nothing* on the other level (state `a|b|c`). The resulting graph is exactly the graph of the
alternative bunkbed hypergraph percolation at level assignment `σ`. This is the bridge that lets
Hollom's computation (Lemma 3.1) be applied inside the WZ model. -/
theorem wzGraph_abc_eq_alt (σ : Fin 6 → Fin 2) :
    wzGraph hollomTriple hollomT (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)
      = altBBGraph hollomE hollomT σ := by
  sorry

end BunkbedAux
