-- Prove2me | Theorems.Thm_CircTrichotomy_lemma_A_3
-- name    : CircTrichotomy.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:53.544586+00:00
-- url     : https://prove2.me/theorems/86790031-0508-401e-8945-f646e1f126a6
-- title:
--   Lemma A.3 — syntactic fibres reduce to the language [GM26b]
-- statement:
--   **Lemma A.3** ([GM26b, Lemma 3.8]). Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language. Then for every $x\in S(L)$,
--   $$\eta_L^{-1}(x)\le L,$$
--   where $\le$ is the rational truth-table reduction (a length-multiplying morphism followed by a finite Boolean combination of quotients).
--
--   Combined with Theorem A.4, a lower bound for one syntactic fibre transfers to $L$. Proved in [GM26b] (arXiv:2609.18484).
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L (Mathlib: accepted by a finite automaton), [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular, recognizable by a finite semigroup, and accepted by a finite automaton; L ⊆ Σ⁺ is [] ∉ L
--   - encoding: η_L⁻¹(x) ≤ L → Reduces (syntPreimage L x) L with positive quotients and the Boolean combination inside Σ⁺; reason: all languages are positive (p.16); quotients are the positive quotients of p.16
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Lemma A.3, p.19

import Mathlib
import Definitions.Def_CircTrichotomy_syntMorphism
import Definitions.Def_CircTrichotomy_Reduces

set_option autoImplicit false

namespace CircTrichotomy

/-- **Lemma A.3 ([GM26b, Lemma 3.8])** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Lemma A.3, p.19; cited from Göller, Manuel,
arXiv:2609.18484): "Let L be a regular language. Then for each x ∈ S(L) we have η_L⁻¹(x) ≤ L."

**Formalization Note** `η_L⁻¹(x)` is the language `syntPreimage L x ⊆ Σ⁺`; `≤` is `Reduces`
(§A.4.3). Languages are positive (`[] ∉ L`, p.16). -/
theorem lemma_A_3 {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) (x : SyntSemigroup L) : Reduces (syntPreimage L x) L := by sorry

end CircTrichotomy
