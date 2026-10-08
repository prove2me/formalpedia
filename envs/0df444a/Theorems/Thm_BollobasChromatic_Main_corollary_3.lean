-- Prove2me | Theorems.Thm_BollobasChromatic_Main_corollary_3
-- name    : BollobasChromatic.Main.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:07:35.937619+00:00
-- url     : https://prove2.me/theorems/3aedd30f-cd16-4b86-a3e5-2cbdd8f52447
-- title:
--   Corollary 3, p. 52 — if E(r',n') = n^α and 2n^{3β} log n ≤ n^{2α} = o(n^{4β}/(log n)⁸), a.e. G_p has a K^{r'} in every n'-set
-- statement:
--   Let $0<p<1$ be fixed. Let $n'=n'(n)$, $r'=r'(n)$, $\alpha=\alpha(n)$ and $\beta=\beta(n)$ be such that, for all large $n$,
--   1. $n'=n^\beta\le n$ and $r'\ge 3$;
--   2. $E(n',r')=\binom{n'}{r'}p^{\binom{r'}2}=n^\alpha$;
--   3. $2n^{3\beta}\log n\le n^{2\alpha}$;
--
--   and such that $n^{2\alpha}=o\bigl(n^{4\beta}/(\log n)^8\bigr)$. Then almost every $G_p=G_{n,p}$ is such that every set of $n'$ vertices contains a complete graph of order $r'$:
--   $$
--   \mathbb P\bigl(\text{every } n'\text{-subset of }[n]\text{ contains a }K^{r'}\text{ in }G_p\bigr)\longrightarrow 1\qquad(n\to\infty).
--   $$
--
--   Applied to the complement $G_q$, $q=1-p$, it says that every not-too-small vertex set of $G_p$ contains a large independent set, which is what the colouring in the proof of Theorem 4 needs.
--
--   **Formalization Note** $E(n',r')$ is the expected number of $K^{r'}$ in $G_{n',p}$ and is equated to a power of $n$, not of $n'$, as on the page. All hypotheses are required only for all large $n$; $p$ is fixed (the standing assumption of §1).
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 52, Corollary 3

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem corollary_3 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n' r' : ℕ → ℕ) (α β : ℕ → ℝ)
    (hn' : ∀ᶠ n : ℕ in atTop, (n' n : ℝ) = (n : ℝ) ^ β n ∧ n' n ≤ n)
    (hr' : ∀ᶠ n : ℕ in atTop, 3 ≤ r' n)
    (hE : ∀ᶠ n : ℕ in atTop, expCliques (n' n) p (r' n) = (n : ℝ) ^ α n)
    (hlow : ∀ᶠ n : ℕ in atTop, 2 * (n : ℝ) ^ (3 * β n) * Real.log (n : ℝ) ≤ (n : ℝ) ^ (2 * α n))
    (hsmall : (fun n : ℕ => (n : ℝ) ^ (2 * α n)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (4 * β n) / Real.log (n : ℝ) ^ 8)) :
    AlmostEvery p (fun n G => ∀ S : Finset (Fin n), S.card = n' n →
      ∃ T ⊆ S, G.IsNClique (r' n) T) := by sorry

end BollobasChromatic.Main
