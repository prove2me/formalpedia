-- Prove2me | Theorems.Thm_EthierKurtz_oblique_graph_exponent_closure
-- name    : EthierKurtz.oblique_graph_exponent_closure
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T20:56:56.126392+00:00
-- url     : https://prove2.me/theorems/12a85f00-447e-4e2a-9456-14560eab3b46
-- title:
--   The exact oblique diffusion graph at a smaller Hoelder exponent lies in the closure of the graph
-- statement:
--   Under the hypotheses of the parent (bounded open $\Omega\subset\mathbb R^{n+1}$ with $C^{2,\mu}$ boundary, outward unit normal $\nu$, $\mu$-Hoelder $a$ and $b$, $C^{1,\mu}$ oblique field $c$ with $c\cdot\nu\ge\varepsilon>0$, $0<\mu\le1$), for every $0<\mu'\le\mu$
--   $$\texttt{obliqueDiffusionGraph}\,\Omega\,\mu'\,a\,b\,c\subseteq\overline{\texttt{obliqueDiffusionGraph}\,\Omega\,\mu\,a\,b\,c}.$$
--
--   Role: the closure of the graph does not depend on the Hoelder exponent, so the dense-range statement proved for exponents below one transfers to the parent's exponent.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Sections 6.7 and 7.2

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_graph_exponent_closure (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (μ' : ℝ) (hμ' : 0 < μ' ∧ μ' ≤ μ) :
    obliqueDiffusionGraph Ω μ' a b c ⊆ closure (obliqueDiffusionGraph Ω μ a b c) := by sorry

end EthierKurtz
