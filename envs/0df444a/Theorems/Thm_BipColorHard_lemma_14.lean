-- Prove2me | Theorems.Thm_BipColorHard_lemma_14
-- name    : BipColorHard.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:45.763529+00:00
-- url     : https://prove2.me/theorems/de51ec1a-c17a-4125-b09e-13a67424cb5f
-- title:
--   Lemma 14 — the partition function of $H_F$ encodes MaxCut
-- statement:
--   Let $q=2k+1\ge3$, $u\in(0,1/k)$, $g>0$, and let $\varepsilon=1/100$. Let $K_L$ have constants $b>0$, $\theta>1$ as in Lemma 11, and fix $\ell\ge1$ such that $\beta=\theta^\ell$ satisfies $\beta^g\ge2^{24}$. There are positive integers $t,M,D_0,C_1$ and a real $\lambda>0$ such that for every graph $F$ with $n>0$ vertices, $m$ edges, maximum degree at most three, and no isolated vertex, the graph $H_F$ is a bipartite multigraph of maximum degree at most $D_0$ with at most $C_1n$ vertices, and
--   $$2^{-n}\beta^{\mathrm{MaxCut}(F)}\le\frac{Z_W(H_F)}{(Q(k+1))^{c_F}\lambda^m}\le e^{2\varepsilon n}2^n\beta^{\mathrm{MaxCut}(F)},$$
--   where $Q=|\Omega|$ and $c_F$ is the number of connected components of $F$.
--
--   This is the estimate that lets an approximation of $Z_W(H_F)$ decide gap MAX-CUT.
--
--   Differences from the source:
--   - generalization: $s,L,\ell$ fixed from Lemmas 10, 11 and (16), depending only on $q$ and $u$ → every $s,L,\ell,b,\theta$ with the conclusion of Lemma 11 for $K_L$ and (16); reason: §4.1 uses $K_L$ only through Lemma 11, so this specializes to the source, and $t,M,D_0,C_1,\lambda$ do not depend on $F$
--   - encoding: an instance $(F,\tau)$ as above → the graph $F$ alone; reason: $\tau$ does not occur in (17)
--   - encoding: terminals allocated freely → terminals indexed by darts and copy numbers; reason: the manuscript requires only distinct terminals, so this is an allocation it allows
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 14, (16), (17), pp.14–15 (PDF pp.16–17)

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_HF
import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false

namespace BipColorHard

open NSWApxHard.Reduction (GraphInput) in
/-- **Lemma 14**, p.15 (PDF p.17), manuscript sha256 78a66d1f…, for `q = 2k + 1 ≥ 3`, `u ∈ (0, 1/k)`, disjoint `A₀, B₀ ∈ Ω`. Let `s`, `L` be such that `K_L` has `b > 0`, `θ > 1`
as in Lemma 11, and let `ℓ ≥ 1` be such that `β = θ^ℓ` satisfies `β^g ≥ 2²⁴` (16). There are positive integers `t, M, D₀, C₁` and a real `λ > 0` such that the
following holds for every graph `F` with `n > 0` vertices, `m` edges, maximum degree at most three and no isolated vertices. `H_F` is a bipartite multigraph of
maximum degree at most `D₀` with at most `C₁n` vertices, and
`2^{-n} β^{MaxCut(F)} ≤ Z_W(H_F) / ((Q(k+1))^{c_F} λ^m) ≤ e^{2εn} 2^n β^{MaxCut(F)}`, (17), with `ε = 1/100`, `Q = |Ω|` and `c_F` the number of connected components of `F`.

**Formalization Note.** The manuscript's instance is `(F, τ)`, and `τ` plays no role in (17). It fixes `s`, `L`, `ℓ` depending only on `q` and `u`, and then `t, M, D₀, C₁, λ`
depending only on `q` and `u`; here the statement holds for every such choice, so `t, M, D₀, C₁, λ` depend on the data before the `∃` and on nothing about `F`. -/
theorem lemma_14 (k : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1 / (k : ℝ))
    (g : ℚ) (hg : 0 < g) (A0 B0 : Omega k) (hdisj : Disjoint A0.1 B0.1)
    (s L ℓ : ℕ) (b θ : ℝ) (hAF : ConnAntiferro (connKL k s u L A0 B0) A0 B0 b θ) (hℓ : 1 ≤ ℓ)
    (h16 : (2 : ℝ) ^ 24 ≤ (θ ^ ℓ) ^ (g : ℝ)) :
    ∃ t M D0 C1 : ℕ, 0 < t ∧ 0 < M ∧ 0 < D0 ∧ 0 < C1 ∧ ∃ lam : ℝ, 0 < lam ∧
      ∀ F : GraphInput, 0 < F.N → MaxDegLe 3 F → (∀ v, ∃ w, F.G.Adj v w) →
        MultiDegLe (HFEdges F ℓ s t L M) D0 ∧
        Fintype.card (HFL F ℓ s t) + Fintype.card (HFR F ℓ s t) ≤ C1 * F.N ∧
        (2 : ℝ) ^ (-(F.N : ℝ)) * (θ ^ ℓ) ^ IIDMatchHard.maxCut F.G ≤
            multiZ k u (HFEdges F ℓ s t L M) /
              (((Nat.choose (2 * k + 1) k : ℝ) * ((k : ℝ) + 1)) ^ Nat.card F.G.ConnectedComponent *
                lam ^ IIDMatchHard.numEdges F.G) ∧
          multiZ k u (HFEdges F ℓ s t L M) /
              (((Nat.choose (2 * k + 1) k : ℝ) * ((k : ℝ) + 1)) ^ Nat.card F.G.ConnectedComponent *
                lam ^ IIDMatchHard.numEdges F.G) ≤
            Real.exp (2 * (1 / 100) * (F.N : ℝ)) * (2 : ℝ) ^ (F.N : ℝ) *
              (θ ^ ℓ) ^ IIDMatchHard.maxCut F.G := by sorry

end BipColorHard
