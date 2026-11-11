-- Prove2me | Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_theorem_3_1
-- name    : AlgoPrinciplesMulticlass.NoEnvelope.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:28:12.320744+00:00
-- url     : https://prove2.me/theorems/924a162f-3740-45ef-8d4b-17cd73b40482
-- title:
--   Theorem 3.1 — a learnable multiclass class that cannot be embedded into any properly learnable class
-- statement:
--   In realizable multiclass PAC learning (§2), a class $\mathcal H\subseteq Y^X$ is **learnable** if some learner $A:(X\times Y)^{<\omega}\to Y^X$ PAC learns it, and **properly learnable** if some learner whose outputs always lie in $\mathcal H$ PAC learns it; PAC learning asks, for every $\varepsilon,\delta\in(0,1)$, one sample size $n_A(\varepsilon,\delta)$ such that $\Pr_{S\sim D^m}[L_D(A(S),h^\star)>\varepsilon]\le\delta$ for all $m\ge n_A(\varepsilon,\delta)$, every target $h^\star$ in the class and every distribution $D$ on $X$.
--
--   **Theorem 3.1.** There exist a domain $X$, a label set $Y$ and a learnable class $\mathcal H\subseteq Y^X$ that cannot be embedded into any properly learnable class: for every $\mathcal H_{\mathrm{prop}}\subseteq Y^X$,
--   $$\mathcal H\subseteq\mathcal H_{\mathrm{prop}}\ \Longrightarrow\ \mathcal H_{\mathrm{prop}}\text{ is not properly learnable.}$$
--
--   This resolves Open Problem 3 of the paper (Conjecture 18 of [ADD+25], in the converse direction): learnability of a multiclass problem does not reduce to proper learnability of some larger class.
--
--   **Formalization Note.** The statement is `∃ (X Y : Type) (Hc : Set (X → Y)), PACLearnable Hc ∧ ∀ Hprop, Hc ⊆ Hprop → ¬ ProperlyPACLearnable Hprop`, with the notions of the definition `PAC`: learners on `Fin m → X × Y` samples of every size, distributions are probability measures for the σ-algebra `⊤` fixed inside the definition, and `Hprop` ranges over all subsets of `X → Y` (no countability, closedness or finite-range restriction).
--
--   Differences from the source:
--   - encoding: "a learnable multiclass hypothesis class H" on some domain and label set; "any properly learnable class Hprop" with H ⊆ Hprop → `∃ X Y : Type, ∃ Hc : Set (X → Y)`, every `Hprop : Set (X → Y)` over the same X and Y, the §2 notions with distributions for the σ-algebra ⊤; reason: the theorem's "That is" clause fixes X and Y; the constructed X is countable, where σ-algebra ⊤ gives exactly the distributions
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 16, Theorem 3.1

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-- Theorem 3.1 (p. 16): there are a domain `X`, a label set `Y` and a learnable class
`H ⊆ Y^X` such that no class `H_prop ⊆ Y^X` containing `H` is properly learnable. -/
theorem theorem_3_1 :
    ∃ (X : Type) (Y : Type) (Hc : Set (X → Y)), PACLearnable Hc ∧
      ∀ Hprop : Set (X → Y), Hc ⊆ Hprop → ¬ ProperlyPACLearnable Hprop := by sorry

end AlgoPrinciplesMulticlass.NoEnvelope
