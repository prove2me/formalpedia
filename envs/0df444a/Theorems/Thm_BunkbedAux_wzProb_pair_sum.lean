-- Prove2me | Theorems.Thm_BunkbedAux_wzProb_pair_sum
-- name    : BunkbedAux.wzProb_pair_sum
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T02:40:54.133303+00:00
-- url     : https://prove2.me/theorems/6a2df9bc-a0b8-470c-9dac-86b4aeeab1d8
-- title:
--   $\mathbb{P}^{wz}$ as a sum over pair configurations
-- statement:
--   By definition $\texttt{wzProb}$ is a sum over Wierman--Ziff configurations, that is over functions $\psi$ on $\iota \times \{0,1\}$ assigning a state to each hyperedge on each level, weighted by $\prod_p P(\psi(p))$.
--
--   This lemma re-presents that sum with each hyperedge's two states packaged together. A function on $\iota \times \{0,1\}$ is the same thing as a function $\varphi$ on $\iota$ taking values in $\Upsilon \times \Upsilon$ — the pair $(\text{lower state},\ \text{upper state})$ — and the weight factors accordingly:
--
--   $$\mathbb{P}^{\mathrm{wz}}[x \leftrightarrow y] \;=\; \sum_{\varphi \,:\, \iota \to \Upsilon \times \Upsilon} \Bigl(\prod_i P(\varphi(i)_1)\,P(\varphi(i)_2)\Bigr)\; \mathbf{1}\bigl[x \leftrightarrow y\bigr],$$
--
--   the connectivity being evaluated in the graph realised by the configuration $p \mapsto \varphi(p_1)_1$ or $\varphi(p_1)_2$ according to the level $p_2$.
--
--   The statement holds for an arbitrary index type, vertex type, hypergraph, transversal set, weight function and pair of endpoints, with no hypothesis on $P$.
--
--   **Mathematical role.** Gladkov--Pak--Zimin remark that a configuration may be viewed "not as a function $\psi : H \to \Upsilon$, but as a function from $H$ to $\Upsilon^2$", and this is that change of view made precise. It is the step that makes the refinement of the state space possible: the refinement splits two elements of $\Upsilon \times \Upsilon$, so it can only be applied once the configuration space has been presented as functions *into* $\Upsilon \times \Upsilon$ rather than as functions on a product index set. Everything in the involution argument then takes place over this indexing.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.3 (p. 4): 'one can view a configuration not as a function psi : H -> Upsilon, but as a function from H to Upsilon^2'.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **`wzProb` as a sum over pair configurations.** A Wierman-Ziff configuration, a function on
`ι × Fin 2`, is the same thing as a function assigning to each hyperedge the *pair* of its states
on the two levels, and the configuration weight factors as a product of per-hyperedge pair
weights. -/
theorem wzProb_pair_sum {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → (V × V × V)) (T : Finset V) (P : WZ → ℚ) (x y : V × Fin 2) :
    wzProb t T P x y
      = ∑ φ : ι → WZ × WZ, (∏ i, P (φ i).1 * P (φ i).2) *
          (if (wzGraph t T (fun p => if p.2 = 0 then (φ p.1).1 else (φ p.1).2)).Reachable x y
            then (1 : ℚ) else 0) := by
  sorry

end BunkbedAux
