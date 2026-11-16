-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_7_5
-- name    : CompDesign.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:01:42.902758+00:00
-- url     : https://prove2.me/theorems/ee201eed-187a-42ae-9e0d-18fe970f2889
-- title:
--   Theorem 7.5 — multi-agent combinatorial: the $(L+2)$-branch rule is budget feasible and $\mathbb E[v(S)]\ge\mathrm{OPT}/(4(L+2))$
-- statement:
--   A ground set $A=\{1,\dots,m\}$ is partitioned among $n$ agents, costs are $c_e\ge0$, $B>0$, and $v:2^A\to\mathbb R$ is normalized, monotone and submodular. A large-market parameter $\lambda\in(0,1]$ with $c_e\le\lambda B$ is given ($\lambda=1$: every action is affordable); $q$ and $L$ are defined in (54)–(55). The randomized rule chooses uniformly one of $L+2$ branches: the singleton-prize branch (for a fixed $e^*\in\arg\max_ev(\{e\})$) and the capped branches with scales $R_r=v(A)/(3/2)^r$, $r=0,\dots,L$.
--
--   **Theorem 7.5 (Logarithmic approximation).** The randomized payment rule is cost oblivious and budget feasible: in every branch the payments are nonnegative and sum to at most $B$ at every profile. For every cost vector, every principal-favoring pure Nash equilibrium $S_{sing}$ of the singleton branch and every pure Nash equilibria $S_r$ of the capped branches,
--   $$\mathbb E[v(S)]\ =\ \frac{v(S_{sing})+\sum_{r=0}^Lv(S_r)}{L+2}\ \ge\ \frac{\mathrm{OPT}}{4(L+2)}\ \ge\ \frac{\mathrm{OPT}}{O(\log q+1)}.$$
--   In particular, the price of anarchy is always at most $O(\log m)$: there is an absolute $C>0$ with $4(L+2)\le C(\log q+1)$ for $m\ge1$ and $4(L+2)\le C\log m$ for $m\ge2$.
--
--   The logarithmic guarantee of the single-agent model extends to many agents with combinatorial action sets, matching the lower bound of Theorem 7.4.
--
--   Differences from the source:
--   - reading: "every choice of pure Nash equilibrium in each realized branch" → principal-favoring pure Nash equilibrium in the singleton-prize branch, any pure Nash equilibrium in the capped branches; reason: §7.2 (p.57) fixes principal-favoring tie-breaking for the model, "only used in the singleton-prize branch"; with plain equilibria Lemma 7.2 fails when c_{e*} = B
--   - encoding: general case (c_e ≤ B, q = m) and large-market case (c_e ≤ λB) → one statement for every l ∈ (0,1] with c_e ≤ l·B; reason: l = 1 gives the general case, q = m for m ≥ 1
--   - encoding: e* ∈ argmax_e v({e}) fixed → the statement holds for every such e*; reason: the rule may use any maximizer
--   - reading: ≥ OPT/O(log q + 1); PoA at most O(log m) → ∃ C > 0: 4(L+2) ≤ C(log q + 1) for all m ≥ 1, and 4(L+2) ≤ C·log m for all m ≥ 2, for every l ∈ (0,1]; reason: the O-notation with one absolute constant; L is largest at l = 1 (q = m), so the bound for every l is the paper's "always at most O(log m)"
--   - encoding: cost oblivious → by construction: no branch reads c; reason: the payments are functions of v, B, own, e* and the profile only
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 7.5, §7.2.2, p.61 (PDF 64); (54)–(56), pp.60–61 (PDF 63–64); Lemma 7.2, p.58 (PDF 61)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsCombPNE
import Definitions.Def_CompDesign_Supplement_cappedPay

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 7.5 (Logarithmic approximation), §7.2.2, p.61 (PDF 64) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Assume that `v` is
normalized, monotone, and submodular, and every individual action is affordable. The randomized
payment rule described above is cost oblivious and budget feasible. For every cost vector and every
choice of pure Nash equilibrium in each realized branch, `E[v(S)] ≥ OPT/(4(L + 2)) ≥
OPT/O(log q + 1)`, where `L` and `q` are defined in (55) and (54). In particular, the PoA is always
at most `O(log m)`.

**Formalization Note.** The ground set is `A = Fin m`, owned by `n` agents through `own`. A
large-market parameter `λ ∈ (0,1]` (`l`) with `c_e ≤ λB` is given; `λ = 1` is the general case
"every action affordable" (`q = m` for `m ≥ 1`). `q = blockCount m l`, `L = numScales m l`. The
rule draws uniformly one of `L + 2` branches: the singleton-prize branch for a fixed
`e* ∈ argmax_e v({e})` (every such `e*`), and the capped branches with scales `R_r = v(A)/(3/2)^r`,
`r = 0, …, L`. Cost obliviousness is by construction (no branch reads `c`); budget feasibility is
the first conjunct (nonnegative payments summing to at most `B` at every profile, in every branch).
The equilibrium of the singleton branch is principal-favoring (§7.2, p.57: principal-favoring
tie-breaking, "only used in the singleton-prize branch"); in the capped branches it is any pure Nash
equilibrium. `E[v(S)] = (v(S_sing) + ∑_r v(S_r))/(L + 2)`. The `O`-clauses are read with one
absolute constant `C > 0`: `4(L + 2) ≤ C(log q + 1)` for `m ≥ 1`, and `4(L + 2) ≤ C log m` for
`m ≥ 2`, for every `λ ∈ (0,1]`. -/
theorem theorem_7_5 :
    (∀ (n m : ℕ) (own : Fin m → Fin n) (v : Finset (Fin m) → ℝ) (B : ℝ) (c : Fin m → ℝ) (l : ℝ),
      0 < B → v ∅ = 0 → IsMonotoneSF v → IsSubmodularSF v → 0 < l → l ≤ 1 →
      (∀ e, 0 ≤ c e ∧ c e ≤ l * B) → ∀ estar : Fin m, (∀ e, v {e} ≤ v {estar}) →
        ((∀ S i, 0 ≤ combSingletonPay B own estar S i) ∧
          (∀ S, ∑ i, combSingletonPay B own estar S i ≤ B) ∧
          (∀ r S i, 0 ≤ cappedPay v B (scale v r) own S i) ∧
          (∀ r S, ∑ i, cappedPay v B (scale v r) own S i ≤ B)) ∧
        ∀ (Ssing : Finset (Fin m)) (Sr : ℕ → Finset (Fin m)),
          IsCombPFPNE own (combSingletonPay B own estar) v c Ssing →
          (∀ r, r ≤ numScales m l → IsCombPNE own (cappedPay v B (scale v r) own) c (Sr r)) →
          OPT v B c / (4 * ((numScales m l : ℝ) + 2)) ≤
            (v Ssing + ∑ r ∈ Finset.range (numScales m l + 1), v (Sr r)) /
              ((numScales m l : ℝ) + 2)) ∧
    ∃ C : ℝ, 0 < C ∧
      (∀ m : ℕ, 1 ≤ m → ∀ l : ℝ, 0 < l → l ≤ 1 →
        4 * ((numScales m l : ℝ) + 2) ≤ C * (Real.log (blockCount m l) + 1)) ∧
      (∀ m : ℕ, 2 ≤ m → ∀ l : ℝ, 0 < l → l ≤ 1 →
        4 * ((numScales m l : ℝ) + 2) ≤ C * Real.log m) := by sorry

end CompDesign.Supplement
