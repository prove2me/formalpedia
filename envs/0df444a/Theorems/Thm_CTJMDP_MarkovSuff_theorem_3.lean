-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_theorem_3
-- name    : CTJMDP.MarkovSuff.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:28.137643+00:00
-- url     : https://prove2.me/theorems/66c54bf4-6dd7-4dfc-972d-1015a4e74d34
-- title:
--   Theorem 3, p. 9 — Feller's series P̄ is the minimal solution of Kolmogorov's forward equation (30), unique among [0,1]-valued solutions when P̄(s,X)=1
-- statement:
--   Let $X$ be a standard Borel space and $q$ a **Q-function** (p. 8): for $z\in X$ and $t>0$, $q(z,t,\cdot\setminus\{z\})$ is a finite measure on $X$, measurable in $(z,t)$. Write $q(z,t)=q(z,t,X\setminus\{z\})$ and suppose (28): $\sup_{t>0}q(z,t)<\infty$ for every $z$. Let $\mathcal Y=\{Z\in\mathfrak B(X):\sup_{z\in Z,t>0}q(z,t)<\infty\}$ be the $q$-bounded sets (29). Fix $x\in X$, and let $\bar P(t,Z)=\bar P(0,x;t,Z)=\sum_{n\ge0}\bar P^{(n)}(0,x;t,Z)$ be Feller's series (25)–(27):
--   $$\bar P^{(0)}(u,x;t,Z)=\delta_x(Z)e^{-\int_u^tq(x,s)ds},\qquad \bar P^{(n)}(u,x;t,Z)=\int_u^t\!\int_X e^{-\int_u^wq(x,\theta)d\theta}q(x,w,dy\setminus\{x\})\bar P^{(n-1)}(w,y;t,Z)\,dw.$$
--   Then:
--
--   1. (a) there are Borel sets $X_1\subseteq X_2\subseteq\cdots$ in $\mathcal Y$ with $\bigcup_nX_n=X$;
--   2. (b) for $t>0$ and $Z\in\mathcal Y$, $\bar P$ satisfies Kolmogorov's forward equation
--   $$P(t,Z)=\delta_x(Z)+\int_0^t\!\int_Xq(z,s,Z\setminus\{z\})P(s,dz)\,ds-\int_0^t\!\int_Zq(z,s)P(s,dz)\,ds;\qquad(30)$$
--   3. (c) $\bar P$ is the minimal function that (i) is a measure in $Z$ for fixed $t$, (ii) is measurable in $t$ for fixed $Z$, and (iii) satisfies (b). If $\bar P(s,X)=1$ for some $s>0$, then every $[0,1]$-valued $P$ satisfying (i)–(iii) equals $\bar P$ on $]0,s]$; if $\bar P(t,X)=1$ for all $t>0$, then $\bar P$ is the unique $[0,1]$-valued function satisfying (i)–(iii).
--
--   This is Feller's minimal-solution theorem in the form of Feinberg, Mandava and Shiryaev [9]; applied to the Q-function of a Markov policy it gives Corollary 5.
--
--   **Formalization Note** $\bar P(t,\cdot)$ is exhibited as a measure agreeing with Feller's series on measurable sets. A solution in the sense of Definition 1 is a family of finite measures; (30) is written additively with the subtracted integral finite. Measurability in $t$ is required on $t>0$.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 9, Theorem 3 ([9, Lemma 1(a) and Corollary 7]), (25)–(30); Q-function, p. 8

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Theorem 3 (p. 9; [9, Lemma 1(a) and Corollary 7]). -/
theorem theorem_3 {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (qQ : X → ℝ → Measure X) (hq : IsQFunction qQ)
    (h28 : ∀ z : X, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t : ℝ, 0 < t → qQ z t {z}ᶜ ≤ C)
    (x : X) :
    (∃ Xn : ℕ → Set X, (∀ n, Xn n ∈ YsetQ qQ) ∧ Monotone Xn ∧ ⋃ n, Xn n = univ) ∧
    ∃ Pbar : ℝ → Measure X,
      (∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → Pbar t Z = fellerSeries qQ 0 x t Z) ∧
      IsFwdSolQ qQ x Pbar ∧
      (∀ Q : ℝ → Measure X, IsFwdSolQ qQ x Q →
        ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → Pbar t Z ≤ Q t Z) ∧
      (∀ s : ℝ, 0 < s → Pbar s univ = 1 →
        ∀ Q : ℝ → Measure X, IsFwdSolQ qQ x Q → (∀ t : ℝ, 0 < t → Q t univ ≤ 1) →
          ∀ t ∈ Ioc (0 : ℝ) s, ∀ Z : Set X, MeasurableSet Z → Q t Z = Pbar t Z) ∧
      ((∀ t : ℝ, 0 < t → Pbar t univ = 1) →
        ∀ Q : ℝ → Measure X, IsFwdSolQ qQ x Q → (∀ t : ℝ, 0 < t → Q t univ ≤ 1) →
          ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → Q t Z = Pbar t Z) := by sorry

end CTJMDP.MarkovSuff
