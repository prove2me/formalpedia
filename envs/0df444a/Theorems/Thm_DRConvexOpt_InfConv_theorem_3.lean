-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_theorem_3
-- name    : DRConvexOpt.InfConv.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:30.165276+00:00
-- url     : https://prove2.me/theorems/c68ba35a-a0c1-4cc5-bf22-d65336f0cef9
-- title:
--   Theorem 3, p. 13 — (6) ⟹ (7) ⟹ (3) for the naïve approximation, the infimal convolution bound and the distributionally robust constraint; equivalence if J = 1
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set (4) with confidence sets $\mathcal C_i = \{(z,u) : C_iz + D_iu \preccurlyeq_{\mathcal K_i} c_i\}$, $i \in \mathcal I$, and assume:
--   1. every $\mathcal K_i$ is a proper cone and $0 \le \underline p_i \le \overline p_i \le 1$;
--   2. (C1): $\mathcal C_I$ is bounded and $\underline p_I = \overline p_I = 1$;
--   3. (C2): some $\mathbb P \in \mathcal P$ has $\mathbb P[(\tilde z,\tilde u)\in\mathcal C_i] \in (\underline p_i,\overline p_i)$ whenever $\underline p_i < \overline p_i$;
--   4. (C3): $v(x,z) = \max_{l}\,(S_lz + s_l)^\top x + \mathbf t_l^\top z + t_l$;
--   5. $\{\mathcal I_j\}_{j\in\mathcal J}$ is a partition of $\mathcal I$ (all blocks nonempty) satisfying (N′), with outer approximations $\mathcal P^j$;
--   6. (added) the uniform first-moment bound: for each $j$ there is $M_j$ with $\mathbb E_{\mathbb P}\|\tilde z\| \le M_j$ for all $\mathbb P\in\mathcal P^j$.
--
--   Then for every $x \in \mathbb R^N$ and $w \in \mathbb R$, the naïve approximation (6), the infimal convolution bound (7) and the distributionally robust constraint (3),
--   $$\text{(6)}\ \min_{j\in\mathcal J}\sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(x,\tilde z)]\le w,\qquad \text{(7)}\ \inf_{(y,\delta)\in\Gamma(x)}\sum_{j\in\mathcal J}\delta_j\sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(y_j/\delta_j,\tilde z)]\le w,\qquad \text{(3)}\ \mathbb E_{\mathbb P}[v(x,\tilde z)]\le w\ \ \forall\mathbb P\in\mathcal P,$$
--   satisfy
--   $$\text{(6)} \Longrightarrow \text{(7)} \Longrightarrow \text{(3)},$$
--   and if $J = 1$, then (3) implies both (7) and (6), so all three are equivalent.
--
--   Both (6) and (7) are thus conservative surrogates for (3) when the nesting condition (N) of Theorem 1 fails, and (7) is never looser than (6).
--
--   **Formalization Note** The uniform first-moment bound is **not in the paper**. The printed proof of (6) $\Rightarrow$ (7) uses that $\sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(0,\tilde z)]$ is finite, which fails in general: with $P = 1$, $\mathcal C_1 = [0,\tfrac12]$ (probability $\ge \tfrac12$), $\mathcal C_2 = [0,1]$ (probability 1), the singleton partition, $v(x,z) = z$ and $w = 1$, (6) holds while (7) fails because $\mathcal P^1$ contains $\tfrac12\delta_0 + \tfrac12\delta_M$ for every $M$. The bound holds, for example, when every block contains a bounded confidence set with $\underline p_i = 1$. Indices are 0-based: $\mathcal I$ is `Fin (nI + 1)`, $\mathcal C_I$ is `Fin.last nI`, $\mathcal J$ is `Fin nJ`, and the partition is a surjective block map. Distributions in $\mathcal P$ and $\mathcal P^j$ have finite first moments. (6) and (7) are `EReal`-valued; (3) is in its $\forall$-form. The hypotheses (N′), (C1), proper cones and $0\le\underline p_i\le\overline p_i\le1$ are the paper's setting and are not used by the proof.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 13, Theorem 3 (proof p. 37)

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- Theorem 3, p. 13: under (C1)–(C3) and (N′), with the disclosed added assumption
`UnifFirstMoment`, (6) ⟹ (7) ⟹ (3), and the reverse implications hold if `J = 1`.
Indices are 0-based; `C_I` is `d.conf (Fin.last nI)`; the partition is given by the surjective
block map `blk`, with `𝒥 = Fin nJ`. -/
theorem theorem_3 {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (blk : Fin (nI + 1) → Fin nJ) (hblk : Function.Surjective blk)
    (hK : ∀ i, IsProperCone (d.K i))
    (hp : ∀ i, 0 ≤ d.plo i ∧ d.plo i ≤ d.phi i ∧ d.phi i ≤ 1)
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hC2 : ∃ μ ∈ ambiguitySet d, ∀ i, d.plo i < d.phi i →
      μ.real (d.conf i) ∈ Set.Ioo (d.plo i) (d.phi i))
    (hN' : WeakNesting d blk) (hFM : UnifFirstMoment d blk)
    (x : Fin nN → ℝ) (w : ℝ) :
    (naiveBound d blk v x ≤ (w : EReal) → infConvBound d blk v x ≤ (w : EReal)) ∧
    (infConvBound d blk v x ≤ (w : EReal) →
      ∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) ∧
    (nJ = 1 → (∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) →
      infConvBound d blk v x ≤ (w : EReal) ∧ naiveBound d blk v x ≤ (w : EReal)) := by sorry

end DRConvexOpt.InfConv
