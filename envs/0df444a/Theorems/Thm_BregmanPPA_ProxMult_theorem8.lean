-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_theorem8
-- name    : BregmanPPA.ProxMult.theorem8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:11.310233+00:00
-- url     : https://prove2.me/theorems/48453563-8b66-4970-b5b0-b5f396f88d4f
-- title:
--   Theorem 8 — nonquadratic proximal methods of multipliers converge to a saddle point
-- statement:
--   Consider a problem of the form (10):
--
--   $$\text{minimize } f(x)\quad\text{such that } g_i(x)\le0\ (i=1,\dots,m),\ x\in C,$$
--
--   with $C\subseteq\mathbb R^n$ closed, nonempty and convex and $f,g_1,\dots,g_m$ proper lower semicontinuous convex functions, finite on $C$, and let $l$ be its Lagrangian. Let $\{c_k\}$ be positive scalars bounded away from zero, $h_x$ a Bregman function on $\mathbb R^n$ with zone $S_x\supseteq C$, and $h_p$ a Bregman function on $\mathbb R^m$ with zone $S_p\supseteq\overline{\Omega^+}$ and $\operatorname{im}(\nabla h_p)=\mathbb R^m$. Suppose $\{(x^k,p^k)\}_{k\ge0}\subseteq\mathbb R^n\times\mathbb R^m$ conforms to the recursions
--
--   $$\begin{aligned}x^{k+1}&=\arg\min_{x\in C}\Big\{f(x)+\frac1{c_k}h_p^{*+}\big(\nabla h_p(p^k)+c_kg(x)\big)+\frac1{c_k}D_{h_x}(x,x^k)\Big\},\\ p^{k+1}&=\nabla h_p^{*+}\big(\nabla h_p(p^k)+c_kg(x^{k+1})\big).\end{aligned}\tag{12}$$
--
--   Then:
--
--   1. if (10) has an optimal solution–Lagrange multiplier pair, i.e. a saddle pair $(x^*,p^*)$ with $l(x^*,p)\le l(x^*,p^*)\le l(x,p^*)$ for all $x,p$, then $(x^k,p^k)$ converges to one such pair;
--   2. if (10) has no such pair, at least one of the sequences $\{x^k\}$, $\{p^k\}$ is unbounded.
--
--   With $h_x=\frac12\|\cdot\|^2$ and $h_p=\frac12\|\cdot\|^2$ this is Rockafellar's proximal method of multipliers; other choices of $h_x,h_p$ give nonquadratic versions with the same guarantee.
--
--   **Formalization Note** "Optimal solution–Lagrange multiplier pair" is the saddle inequality, which the paper identifies with these pairs on p. 220 and which is exactly the zero set of $K$ used in the proof. "Converges to one" means both sequences converge, to the two components of a single saddle pair. The page's "$S_p\supset\overline{\Omega^+}$" is read as $\supseteq$ (the paper's typography; $S_p$ is open). The $x$-step uses a minimality predicate instead of $\arg\min$ (equivalent, the minimizer being unique, p. 222); the run requires $x^0\in S_x$ and $p^k\in S_p$; $h_p^{*+}$ enters through `toReal`, exact by Lemma 3. The existence of runs is the separate item `theorem8_existence`. The §4.2 assumption that the dual functional is not everywhere $-\infty$ concerns the dual problem of §4.2 and is not used in §5; it is not assumed, which can only strengthen the statement.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 220–221, Theorem 8 (first two sentences)

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

open Filter Topology

namespace BregmanPPA.ProxMult

/-- Theorem 8, pp. 220–221 (first two sentences): along a run of the nonquadratic proximal
method of multipliers (12), if (10) has a saddle pair (an optimal solution–Lagrange multiplier
pair), then `(x^k, p^k)` converges to one; if it has none, `{x^k}` or `{p^k}` is unbounded. -/
theorem theorem8 {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    ((∃ x' p', IsSaddlePair C f g x' p') →
      ∃ x' p', IsSaddlePair C f g x' p' ∧
        Tendsto x atTop (𝓝 x') ∧ Tendsto p atTop (𝓝 p')) ∧
    ((¬ ∃ x' p', IsSaddlePair C f g x' p') →
      ¬ Bornology.IsBounded (Set.range x) ∨ ¬ Bornology.IsBounded (Set.range p)) := by sorry

end BregmanPPA.ProxMult
