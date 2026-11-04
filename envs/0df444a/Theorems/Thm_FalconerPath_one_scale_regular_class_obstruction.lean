-- Prove2me | Theorems.Thm_FalconerPath_one_scale_regular_class_obstruction
-- name    : FalconerPath.one_scale_regular_class_obstruction
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:31.42521+00:00
-- url     : https://prove2.me/theorems/e9eda362-f4ee-4739-905d-91ea3c6812c0
-- title:
--   Failure of uniform gain yields obstructing regular classes
-- statement:
--   Fix $k\ge2$, $k-\tfrac12<s<k$, $k-1\le q<k-\tfrac12$, and $\zeta,L,a,K,C>0$. Suppose the uniform forward-gain assertion fails. That assertion would give fixed $\varepsilon,c,D>0$ and $N_0$ working for every $N\ge N_0$, every pair of probabilities in $\mathbb R^{k+1}$ with support radius $L$, separation $a$, and all-scale $s$-ball constant $K$, and every Borel relation with cap bounds $2^{\varepsilon N}u^q$ and plate bounds $Cu^\zeta$ in both orientations for $2^{-N}\le u\le1$. Its desired conclusion is a Borel subrelation deleting at most $D2^{-cN}$ product mass and bounding all radius-$2^{-N}$ forward caps by $2^{-N(q+c)}$ at almost every pin.
--
--   Then there are positive constants $L^\prime,a^\prime,C^\prime$ and a sequence of normalized regular-class data with these fixed geometry and plate constants, such that $N_j\to\infty$ and $h_j\to0$. For every $c,D>0$, for all sufficiently large $j$ there is no Borel $H\subset G_j$ for which
--
--   $$(\nu_j\otimes\rho_j)(G_j\setminus H)\le DR_j^{-c}$$
--
--   and every radius-$R_j^{-1}$ forward cap of $(\pi_x)_\#(\rho_j|_{H_x})$ has mass at most $R_j^{-q-c}$ for $\nu_j$-almost every $x$.
--
--   Here a normalized regular-class datum consists of an integer $N_j$, probabilities $\nu_j,\rho_j$ on $\mathbb R^{k+1}$ with supports in $\overline B(0,L^\prime)$ and cross distances at least $a^\prime$, a translated half-open unit root carrying $\rho_j$, a nonnegative error $h_j$, and a profile $m_j$ with $m_j(0)=0$, nondecreasing and $(k+1)$-Lipschitz on $[0,1]$, satisfying $m_j(u)\ge su-h_j$. In its translated dyadic grid, every occupied depth-$b$ cell has $\rho_j$-mass between $R_j^{-m_j(b/N_j)-h_j}$ and $R_j^{-m_j(b/N_j)+h_j}$, for $b\le N_j$, where $R_j=2^{N_j}$. For occupied nested cells $P\subset Q$ at depths $c\ge b$, $c\le N_j$, the ratio $\rho_j(P)/\rho_j(Q)$ lies between $R_j^{-[m_j(c/N_j)-m_j(b/N_j)]-h_j}$ and $R_j^{-[m_j(c/N_j)-m_j(b/N_j)]+h_j}$. The datum includes a Borel $G_j\subset\operatorname{supp}\nu_j\times\operatorname{supp}\rho_j$ such that, for $\rho_j$-almost every $z$, the unnormalized reverse law $(\pi_z)_\#(\nu_j|_{G_j^z})$ obeys cap bounds $R_j^{h_j}u^q$ and directional plate bounds $C^\prime u^\zeta$ for $R_j^{-1}\le u\le1$. The geometry constants $L^\prime,a^\prime$ are positive. The Lean statement isolates a sequential obstruction from the proof rather than asserting a new numbered paper result.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale, proof paragraph beginning “We prove this assertion by contradiction”, together with the final paragraph beginning “Choose the regularization parameter” and its recombination with original source weights.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem one_scale_regular_class_obstruction {k : ℕ} (hk : 2 ≤ k)
    (s q ζ L a K C : ℝ) (hs : (k:ℝ)-1/2 < s) (hsk : s < k)
    (hq : (k:ℝ)-1 ≤ q) (hqS : q < (k:ℝ)-1/2)
    (hζ : 0 < ζ) (hL : 0 < L) (ha : 0 < a) (hK : 0 < K) (hC : 0 < C)
    (hfail : ¬ ForwardGain k s q ζ L a K C) :
    ∃ L' a' C' : ℝ, 0 < L' ∧ 0 < a' ∧ 0 < C' ∧
      ∃ X : ℕ → RadialClassData k s q ζ L' a' C',
        Tendsto (fun j => (X j).N) atTop atTop ∧
        Tendsto (fun j => (X j).err) atTop (𝓝 0) ∧
        ∀ c D : ℝ, 0 < c → 0 < D → ∀ᶠ j in atTop,
          ¬ ∃ H : PairSet (k+1), MeasurableSet H ∧ H ⊆ (X j).G ∧
            ((X j).ν.prod (X j).ρ) ((X j).G \ H) ≤
              ENNReal.ofReal (D*(scale (X j).N)^(-c)) ∧
            ∀ᵐ x ∂(X j).ν, ∀ w ∈ unitSphere (k+1),
              forwardDirection (X j).ρ H x (Metric.ball w (mesh (X j).N)) ≤
                ENNReal.ofReal ((scale (X j).N)^(-q-c)) := by sorry
end FalconerPath
