-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_lemma_4_4
-- name    : AffinePolicyOpt.OneDim.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:08:06.050802+00:00
-- url     : https://prove2.me/theorems/bc078d04-07b8-42fd-b280-4e9f351c41b3
-- title:
--   Lemma 4.4, p. 15 — System (37) is feasible, and its solutions satisfy −b_i ≤ q_i ≤ 0 and L ≤ q(w) ≤ U on the hypercube
-- statement:
--   Work in the setting of the induction step: generators $a,b\in\mathbb R^k$ with $b_i>0$ and $a_1/b_1>\dots>a_k/b_k$, offsets $a_0,b_0$, $\theta=\pi(w)$ on $\mathcal H_k=[0,1]^k$, $c\ge0$, $L\le U$, a real $y^*$, the clamped law $u^*(\theta_2)=\max(L,\min(U,y^*-\theta_2))$, the right-side vertices $v_i=\pi(1,\dots,1,0,\dots,0)$ and their images $\tilde v_i$ (29). Assume:
--
--   1. case [C4]: the zonogon is neither entirely below the band $\mathcal B_{LU}=\{\theta_2\in[y^*-U,y^*-L]\}$ ($\theta_2[v_k]<y^*-U$), nor inside it, nor entirely above it ($\theta_2[v_0]>y^*-L$);
--   2. $t$ is the index (31): the number of generators with $a_i/b_i>c$;
--   3. (Lemma 4.3, part 1) for some $s\le r\le k$, $\operatorname{r-side}(\Delta_\Gamma)=\{\tilde v_0,\dots,\tilde v_s\}\cup\{\tilde v_t\}\cup\{\tilde v_r,\dots,\tilde v_k\}$, where $\Delta_\Gamma=\operatorname{conv}\{\tilde v_0,\dots,\tilde v_k\}$;
--   4. (Lemma 4.3, part 2, (34)) $\cot(\tilde v_s,\tilde v_{\min(t,r)})\ge a_{s+1}/b_{s+1}$ when $t>s$, and $\cot(\tilde v_{\max(t,s)},\tilde v_r)\le a_r/b_r$ when $t<r$.
--
--   Then System (37),
--   $$q_0+\dots+q_i=u^*(v_i)\ \ (i\in\{0..s\}\cup\{t\}\cup\{r..k\}),\quad \frac{a_i+c q_i}{b_i+q_i}=K_U\ (s<i\le\min(t,r)),\quad \frac{a_i+c q_i}{b_i+q_i}=K_L\ (\max(t,s)<i\le r),$$
--   has a solution, and every solution satisfies
--   $$-b_i\le q_i\le0\quad(i=1,\dots,k),\qquad L\le q_0+\sum_{i=1}^kq_iw_i\le U\quad\text{for all }w\in[0,1]^k.$$
--
--   This is the robust feasibility half of the induction step: the affine controller built by Algorithm 1 respects the control bounds for every disturbance.
--
--   **Formalization Note** Lemma 4.3's conclusions are taken as hypotheses (Lemma 4.3 is not formalized here); the matched indices are the listed index set. The alignment rows and the cotangent inequalities (34) are cross-multiplied, and the index (31) is encoded as "$i\le t$ exactly when $c\,b_i<a_i$", which is (31) under the ordering (32). The hypothesis $b_i>0$ is added: the page divides by $b_i$ in (31), (32) and (34). The law $u^*$ is the clamp for an arbitrary real $y^*$; the lemma does not use that $y^*$ is a minimizer.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 15, Lemma 4.4, with Algorithm 1 and System (37) (p. 14), cases [C1]–[C4] (p. 11), (31)–(32) and Lemma 4.3 (p. 12)

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

namespace AffinePolicyOpt.OneDim

/-- Lemma 4.4: in case [C4], with the right side of `Δ_Γ` as in Lemma 4.3
(`{ṽ_0,…,ṽ_s} ∪ {ṽ_t} ∪ {ṽ_r,…,ṽ_k}`, with (34)), system (37) is feasible, and every solution
satisfies `−b_i ≤ q_i ≤ 0` and `L ≤ q(w) ≤ U` on the hypercube. -/
theorem lemma_4_4 (k : ℕ) (a0 b0 : ℝ) (a b : Fin k → ℝ) (hb : ∀ i, 0 < b i)
    (hab : GenOrdered a b) (c L U ystar : ℝ) (hc : 0 ≤ c) (hLU : L ≤ U)
    -- case [C4]: none of [C1], [C2], [C3]
    (hC4 : ¬ ((zon a0 b0 a b (prefixVertex k k)).2 < ystar - U) ∧
      ¬ (ystar - U ≤ (zon a0 b0 a b (prefixVertex k 0)).2 ∧
          (zon a0 b0 a b (prefixVertex k k)).2 ≤ ystar - L) ∧
      ¬ (ystar - L < (zon a0 b0 a b (prefixVertex k 0)).2))
    -- the index `t` of (31)
    (t : ℕ) (htk : t ≤ k) (ht : ∀ g : Fin k, (g : ℕ) < t ↔ c * b g < a g)
    -- Lemma 4.3, part 1
    (s r : ℕ) (hsr : s ≤ r) (hrk : r ≤ k)
    (hside : rside (convexHull ℝ
        (Set.range (fun i : Fin (k + 1) => vtilde a0 b0 a b c L U ystar (i : ℕ)))) =
      (fun i => vtilde a0 b0 a b c L U ystar i) '' matchedIdx k s r t)
    -- Lemma 4.3, part 2: (34), cross-multiplied
    (h34a : s < t → ∀ g : Fin k, (g : ℕ) = s →
      a g * ((vtilde a0 b0 a b c L U ystar (min t r)).2 - (vtilde a0 b0 a b c L U ystar s).2) ≤
        b g * ((vtilde a0 b0 a b c L U ystar (min t r)).1 - (vtilde a0 b0 a b c L U ystar s).1))
    (h34b : t < r → ∀ g : Fin k, (g : ℕ) + 1 = r →
      b g * ((vtilde a0 b0 a b c L U ystar r).1 -
          (vtilde a0 b0 a b c L U ystar (max t s)).1) ≤
        a g * ((vtilde a0 b0 a b c L U ystar r).2 -
          (vtilde a0 b0 a b c L U ystar (max t s)).2)) :
    (∃ (q0 : ℝ) (q : Fin k → ℝ) (KU KL : ℝ), System37 a0 b0 a b c L U ystar s r t q0 q KU KL) ∧
    ∀ (q0 : ℝ) (q : Fin k → ℝ) (KU KL : ℝ), System37 a0 b0 a b c L U ystar s r t q0 q KU KL →
      (∀ i, -b i ≤ q i ∧ q i ≤ 0) ∧
      ∀ w ∈ cube k, L ≤ q0 + ∑ i, q i * w i ∧ q0 + ∑ i, q i * w i ≤ U := by sorry

end AffinePolicyOpt.OneDim
