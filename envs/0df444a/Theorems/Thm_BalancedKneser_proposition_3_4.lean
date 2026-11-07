-- Prove2me | Theorems.Thm_BalancedKneser_proposition_3_4
-- name    : BalancedKneser.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:43.352862+00:00
-- url     : https://prove2.me/theorems/740da488-cbee-49c9-903c-7546fce39c50
-- title:
--   Proposition 3.4 — the general coloring criterion $\chi(G)\ge d+3$ (corrected: connectivity includes nonemptiness)
-- statement:
--   Let $G$ be a finite simple graph and $d\ge1$, and suppose that $N(G)$ is $(d-1)$-connected (nonempty, and maps of spheres of dimension $\le d-1$ extend over balls). Let $(S_\alpha)_\alpha$ be a family of vertex sets of $G$ such that the images of
--   $$
--   H_d\big(N(G)[S_\alpha];\mathbb F_2\big)\longrightarrow H_d\big(N(G);\mathbb F_2\big)
--   $$
--   under the inclusions of the induced subcomplexes span $H_d(N(G);\mathbb F_2)$; this holds in particular when cycles $z_\alpha$ supported on $S_\alpha$ generate $H_d(N(G);\mathbb F_2)$. If every proper coloring of $G$ with colors in $[d+2]$ uses at most $d+1$ colors on each $S_\alpha$, then
--   $$
--   \chi(G)\ \ge\ d+3 .
--   $$
--
--   The six-color and ten-color lower bounds of Theorem 1.2 are the cases $d=3$ (pentagon cycles) and $d=7$ (rook cycles).
--
--   **Formalization Note** Homology is singular homology of realizations; $\chi$ is `SimpleGraph.chromaticNumber`, in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - correction: t-connected as printed (p.6), which the empty space satisfies → IsConnectedUpTo also requires nonemptiness; reason: counterexample to the printed proposition: G edgeless on one vertex, d = 1, the empty family of cycles (which generates H₁(∅) = 0); every hypothesis holds, but χ(G) = 1 < 4
--   - generalization: cycles z_α generate H_d(N(G); F₂), and colorings use at most d + 1 colors on the support of each z_α → vertex sets S α whose induced subcomplexes' H_d-images span H_d(N(G); F₂), and colorings use at most d + 1 colors on each S α; reason: a cycle supported on S α has its class in the image of H_d(N(G)[S α]), so the source's hypothesis (with S α the support of z_α) implies the Lean one; the conclusion is the same
--   - reading: a graph G → a finite simple graph (Fintype V); reason: the proof (§9.1, p.17) uses that B(G) is a finite free Z₂-CW complex; every graph the paper applies the lemma to is finite
--   - encoding: simplicial homology of the complex → singular homology of its geometric realization (Hatcher.Singular.H); reason: the two agree for finite simplicial complexes; same groups
--   - encoding: χ(G) ≥ d + 3 → ((d + 3 : ℕ) : ℕ∞) ≤ G.chromaticNumber; reason: Mathlib's chromatic number is ℕ∞-valued; same statement for finite graphs
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Proposition 3.4, p.8 (PDF p.10); t-connected, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_Hatcher_SingularHomology
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_BalancedKneser_inclusionMap
import Definitions.Def_BalancedKneser_nbhdComplex
import Definitions.Def_BalancedKneser_IsConnectedUpTo

namespace BalancedKneser

/-- **Proposition 3.4** (Alipour–Jafari, arXiv:2611.04486v1, p.8 (PDF p.10)), with the corrected
connectivity convention: "Let d ≥ 1. Suppose that N(G) is (d − 1)-connected and that cycles z_α
generate H_d(N(G); F2). If every proper (d + 2)-coloring uses at most d + 1 colors on the
support of each z_α, then χ(G) ≥ d + 3."

For a finite simple graph `G`, the generating cycles are described by their supports
`S α ⊆ V(G)`: the hypothesis is that the images of `H_d(|N(G)[S α]|; F₂)` under the inclusions
of the induced subcomplexes span `H_d(|N(G)|; F₂)`. A cycle supported on `S α` has its class in
that image, so the source's hypothesis implies this one.

Formalization Note: homology is singular homology of realizations; `IsConnectedUpTo` requires
nonemptiness (without it the proposition fails for an edgeless graph with `d = 1`); `χ` is
`SimpleGraph.chromaticNumber : ℕ∞`. -/
theorem proposition_3_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (d : ℕ)
    (hd : 1 ≤ d) (hconn : IsConnectedUpTo (TreeCoverLB.realization (nbhdComplex G)) (d - 1))
    {ι : Type} (S : ι → Finset V)
    (hgen : ⨆ α, LinearMap.range (Hatcher.Singular.map (ZMod 2) d
      (inclusionMap (restrict_subset (nbhdComplex G) (S α)))).hom = ⊤)
    (hcol : ∀ κ : G.Coloring (Fin (d + 2)), ∀ α, ((S α).image (fun v => κ v)).card ≤ d + 1) :
    ((d + 3 : ℕ) : ℕ∞) ≤ G.chromaticNumber := by sorry

end BalancedKneser
