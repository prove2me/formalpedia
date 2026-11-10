-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_7
-- name    : CNFLearnMQ.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:53.206379+00:00
-- url     : https://prove2.me/theorems/b061d321-5438-41a3-be90-ae5263510d36
-- title:
--   Lemma 5.7 — ExtendSubclause keeps a strict subclause extension inside the target
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Let $c\in C$ and let $s=(S,\sigma_S)\subseteq c$ be a subclause of width $|S|<k$. Let $Z_1,\dots,Z_N$, $N\ge1$, be solutions violating $s$, and suppose every core recovery succeeds, i.e. the recovered family of $Z_i$ is $\mathcal R_{Z_i}$. Then the extensions accepted by lines 3–9 of Algorithm 4 (with frequencies over the $N$ samples) contain a strict extension $s'$ of $s$ with $s'\subseteq c$.
--
--   This is the first requirement of the extension rule: the output formula never loses a subclause of a target clause, so its solutions are solutions of $\Phi$.
--
--   Differences from the source:
--   - generalization: a rejected candidate $s$ and the $N_{\mathrm{ext}}$ selected pool samples of ExtendSubclause$(s,Y)$ → any $N\ge1$ solutions violating $s$, with frequencies over these $N$ samples; reason: rejection is used only to guarantee that the selected samples exist (p.27), and $N_{\mathrm{ext}}\ge1$
--   - encoding: every core recovery call succeeds; the subroutine returns a strict extension still a subclause of $c$ → recovered families equal `cores Φ Zᵢ`; some $s'\in$ `acceptExtensions` with $s\subseteq s'$, $s'\ne s$, $s'\subseteq c$; reason: direct transcription
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.7, p.27

import Mathlib
import Definitions.Def_CNFLearnMQ_extendSubclause

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.7, p.27 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5, let `s ⊆ c` with `c ∈ C` and
`|S| < k`, and let `Z_1, …, Z_N` (`N ≥ 1`) be solutions violating `s` whose core families are all
recovered exactly. Then the accepted extensions of Algorithm 4 (lines 3–9, frequencies with
denominator `N`) contain a strict extension `s′` of `s` with `s′ ⊆ c`.

**Formalization Note** In the paper `s` is a rejected candidate, which only guarantees that the
`N = N_ext` selected samples exist (p.27); the statement here takes any `N ≥ 1` violating solutions
as given. "Every core recovery call succeeds" is `R̂_{Zᵢ} = R_{Zᵢ}`. `s ⊆ c` is `Subclause s c`, and
"strict extension" is `s ⊆ s′`, `s′ ≠ s`. -/
theorem lemma_5_7 {n k d : ℕ} {t : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n)
    (Φ : CNF n) (hΦ : KD Φ k d) (s c : Clause n) (hc : c ∈ Φ) (hsc : Subclause s c)
    (hs : width s < k) (N : ℕ) (hN : 1 ≤ N) (Zs : List (Assignment n)) (hlen : Zs.length = N)
    (hZ : ∀ Z ∈ Zs, Z ∈ solutions Φ ∧ Violates s Z) :
    ∃ s' ∈ acceptExtensions k N s Zs (Zs.map (cores Φ)),
      Subclause s s' ∧ s' ≠ s ∧ Subclause s' c := by sorry

end CNFLearnMQ
