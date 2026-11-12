-- Prove2me | Theorems.Thm_BunkbedAux_eta_half_reflection
-- name    : BunkbedAux.eta_half_reflection
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T01:03:46.027032+00:00
-- url     : https://prove2.me/theorems/b1553d43-e4d5-4ced-b96e-ee5bb5ee8b98
-- title:
--   The half-reflection involution and its connectivity properties
-- statement:
--   Let $\Lambda = \{abc,\, ab|c,\, ac|b,\, a|b|c\}$ be the Wierman--Ziff state space with the state $a|bc$ removed, and let $\Lambda^2_+$ be the $16$-element set of pairs from $\Lambda$ in which the two pairs $(abc,a|b|c)$ and $(a|b|c,abc)$ are represented by their refined $+$ variants. The *half-reflection* $\eta$ is the identity on
--   $$\Omega_0 = \bigl\{(abc,ac|b),\,(ac|b,abc),\,(a|b|c,ab|c),\,(ab|c,a|b|c),\,(abc,abc),\,(a|b|c,a|b|c),\,(ab|c,ab|c),\,(ac|b,ac|b)\bigr\},$$
--   agrees with the level swap $\rho$ on $\Omega_1 = \{(abc,ab|c),(ab|c,abc),(a|b|c,ac|b),(ac|b,a|b|c)\}$, and on $\Xi$ exchanges
--   $$(abc,a|b|c)^{+} \leftrightarrow (ab|c,ac|b), \qquad (a|b|c,abc)^{+} \leftrightarrow (ac|b,ab|c).$$
--
--   This theorem collects the properties of $\eta$ that the involution argument requires. It is an involution of $\Lambda^2_+$, it preserves $\Lambda^2_+$, and it is **weight-preserving**: the only nonobvious case is $\Xi$, where both $(abc,a|b|c)^{+}$ and $(ab|c,ac|b)$ carry weight $P_{ab|c}P_{ac|b}$. It also commutes with $\rho$, which is what makes the roles of a hyperedge and its mirror image interchangeable.
--
--   The last three conjuncts are Proposition 3.7, the connectivity content. Writing a hyperedge as $(a,b,c)$ with $a$ transversal, and reading the first component of a pair as the lower-level state:
--
--   1. if $b$ and $c$ are joined within the hyperedge, then after applying $\eta$ the first component joins $a$ to $b$ and the second joins $a$ to $c$ — so $b$ reaches $c'$ along $b \to a \to a' \to c'$, using the post at the transversal vertex $a$;
--   2. if $a$ and $b$ are joined, they remain joined;
--   3. if $a$ and $c$ are joined, then $a'$ and $c'$ become joined.
--
--   **Mathematical role.** These three transformations are exactly what is needed to convert a path realising $u_1 \leftrightarrow u_{10}$ into one realising $u_1 \leftrightarrow u_{10}'$, and conversely. Combined with weight preservation they show that the configurations meeting $\Lambda^2_+$ contribute equally to the two connection events and therefore cancel from their difference — which reduces the robustness lemma to the configurations avoiding $\Lambda^2_+$, where the alternative model and Hollom's computation take over.
--
--   **Formalization note.** Every assertion here is a finite check over the $16$ elements of $\Lambda^2_+$, so all but the weight identity are decided by kernel reduction; the weight identity needs a case analysis because the state probabilities are arbitrary rationals.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Definition 3.6 and Proposition 3.7 (pp. 4-5).

import Definitions.Def_BunkbedWZRefined
open Bunkbed.Hyper

namespace BunkbedAux

/-- **The half-reflection involution and its connectivity properties** (Definition 3.6 and
Proposition 3.7 of Gladkov-Pak-Zimin). On the 16-element set `Λ²₊` the map `eta` is a
weight-preserving involution which commutes with the level swap `rho`, and it transforms the
within-hyperedge connections in the three ways needed for the path-surgery argument. -/
theorem eta_half_reflection (P : WZ → ℚ) :
    (∀ q : WZExt, WZExt.inLamSq q = true → WZExt.eta (WZExt.eta q) = q) ∧
    (∀ q : WZExt, WZExt.inLamSq q = true → WZExt.inLamSq (WZExt.eta q) = true) ∧
    (∀ q : WZExt, WZExt.inLamSq q = true → WZExt.wt P (WZExt.eta q) = WZExt.wt P q) ∧
    (∀ q : WZExt, WZExt.inLamSq q = true →
      WZExt.eta (WZExt.rho q) = WZExt.rho (WZExt.eta q)) ∧
    (∀ q : WZExt, WZExt.inLamSq q = true → (WZExt.toPair q).1 = WZ.abc →
       ((WZExt.toPair (WZExt.eta q)).1 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).1 = WZ.ab_c) ∧
       ((WZExt.toPair (WZExt.eta q)).2 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).2 = WZ.ac_b)) ∧
    (∀ q : WZExt, WZExt.inLamSq q = true →
       ((WZExt.toPair q).1 = WZ.abc ∨ (WZExt.toPair q).1 = WZ.ab_c) →
       ((WZExt.toPair (WZExt.eta q)).1 = WZ.abc ∨
         (WZExt.toPair (WZExt.eta q)).1 = WZ.ab_c)) ∧
    (∀ q : WZExt, WZExt.inLamSq q = true →
       ((WZExt.toPair q).1 = WZ.abc ∨ (WZExt.toPair q).1 = WZ.ac_b) →
       ((WZExt.toPair (WZExt.eta q)).2 = WZ.abc ∨
         (WZExt.toPair (WZExt.eta q)).2 = WZ.ac_b)) := by
  sorry

end BunkbedAux
