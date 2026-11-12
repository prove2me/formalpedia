-- Prove2me | Theorems.Thm_BunkbedAux_probOf_image_map
-- name    : BunkbedAux.probOf_image_map
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:58:01.8111+00:00
-- url     : https://prove2.me/theorems/76e614ef-fcd0-4afd-94aa-848205d6284f
-- title:
--   Percolation with constant weights is relabelling-invariant
-- statement:
--   Bernoulli bond percolation should not care how the vertices are named. This theorem is that statement, in the form needed when a gadget is embedded into a larger graph.
--
--   Let $f$ be an injective map of vertex sets, $E$ a finite edge set, and $c$ a constant weight. If an event $\mathcal{E}$ on configurations of $E$ corresponds to an event $\mathcal{E}'$ on configurations of the image — meaning $\mathcal{E}(S) \iff \mathcal{E}'\bigl(\mathrm{Sym}^2(f)[S]\bigr)$ for every $S \subseteq E$ — then
--
--   $$\mathbb{P}_{E,\,c}[\mathcal{E}] \;=\; \mathbb{P}_{\mathrm{Sym}^2(f)[E],\,c}[\mathcal{E}'].$$
--
--   Two things make this work. Injectivity of $f$ makes $\mathrm{Sym}^2(f)$ injective, so taking images is a bijection from the subsets of $E$ onto the subsets of the image, under which the corresponding events match by hypothesis. And with a **constant** weight the configuration weight depends only on the two cardinalities $|S|$ and $|E \setminus S|$, both of which an injective image preserves.
--
--   The constancy hypothesis is genuinely needed in this form: for a general weight function one would have to assume that the weights correspond under $f$, since otherwise the two models assign different probabilities to corresponding configurations. In the application the weight is the constant $1/2$, so the hypothesis costs nothing.
--
--   **Mathematical role.** Together with the transport of reachability along an injective relabelling, this identifies the five partition probabilities of an embedded gadget copy with those of the gadget itself. That identification is what lets the abstract analysis of the gadget — its partition probabilities, and the verification that they satisfy the robustness lemma's conditions — be applied to the copies sitting inside the $7{,}222$-vertex counterexample graph.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4 (pp. 6-7), gadget substitution.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset SimpleGraph

namespace BunkbedAux

/-- **Percolation with constant weights is invariant under injective relabelling.** -/
theorem probOf_image_map {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (E : Finset (Sym2 V)) (c : ℚ)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev]
    (ev' : Finset (Sym2 W) → Prop) [DecidablePred ev']
    (hev : ∀ S, S ⊆ E → (ev S ↔ ev' (S.image (Sym2.map f)))) :
    probOf E (fun _ => c) ev = probOf (E.image (Sym2.map f)) (fun _ => c) ev' := by
  sorry

end BunkbedAux
