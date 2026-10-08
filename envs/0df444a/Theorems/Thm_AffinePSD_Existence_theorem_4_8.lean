-- Prove2me | Theorems.Thm_AffinePSD_Existence_theorem_4_8
-- name    : AffinePSD.Existence.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:14.760769+00:00
-- url     : https://prove2.me/theorems/5d3922b4-76dd-447f-8c57-a5c45e0a0469
-- title:
--   Theorem 4.8 — comparison for matrix ODEs with a quasi-monotone increasing vector field (Volkmann)
-- statement:
--   Let $U\subseteq S_d$ be open (in $S_d$), $T>0$, and $f:[0,T)\times U\to S_d$ continuous and locally Lipschitz in its second argument, locally uniformly in the first, with $f(t,\cdot)$ quasi-monotone increasing on $U$ for every $t\in[0,T)$. Let $0<t_0\le T$ and let $x,y:[0,t_0)\to U$ be differentiable with $x(0)\preceq y(0)$ and
--   $$\dot x(t)-f(t,x(t))\preceq\dot y(t)-f(t,y(t)),\qquad0\le t<t_0.$$
--   Then
--   $$x(t)\preceq y(t)\qquad\text{for all }t\in[0,t_0).$$
--
--   The paper deduces this from a general theorem of Volkmann. It is the tool that keeps the Riccati flow inside the cone and away from its boundary (Proposition 5.3).
--
--   **Formalization Note** "Open in $S_d$" means $U=V\cap S_d$ with $V$ open in $M_d$. "Locally Lipschitz" means: every point of $[0,T)\times U$ has a neighbourhood $N$ in $[0,T)\times U$ and a constant $K$ with $\|f(s,y)-f(s,z)\|\le K\|y-z\|$ whenever $(s,y),(s,z)\in N$. This is weaker than joint local Lipschitz continuity in $(t,x)$, so the statement covers that reading too. All norms on $M_d$ are equivalent and $K$ is existential, so the choice of norm does not matter. The derivatives are one-sided at $t=0$. $T$ is a real number; the case $T=\infty$ follows by applying the statement on every $[0,n)$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Theorem 4.8, p. 22

import Mathlib
import Definitions.Def_AffinePSD_Existence_Cone
import Definitions.Def_AffinePSD_Existence_QuasiMono

open scoped Topology

namespace AffinePSD.Existence

/-- Theorem 4.8 (arXiv:0910.0137v3, §4, p. 22; deduced by the authors from Volkmann's comparison
theorem): let `U ⊂ S_d` be open, `f : [0,T) × U → S_d` continuous, locally Lipschitz and
quasi-monotone increasing in its second argument for every `t`; if `x, y : [0, t₀) → U`
(`0 < t₀ ≤ T`) are differentiable with `x(0) ⪯ y(0)` and
`ẋ(t) − f(t, x(t)) ⪯ ẏ(t) − f(t, y(t))` on `[0, t₀)`, then `x(t) ⪯ y(t)` on `[0, t₀)`.
Formalization Note: `U` open in `S_d` is `U = V ∩ S_d` with `V` open in `M_d`; `f` is defined on
`ℝ × M_d` and only its values on `[0,T) × U` enter; "locally Lipschitz" is joint local Lipschitz
continuity in the state variable, locally uniformly in time: every point of `[0,T) × U` has a
neighbourhood `N` in `[0,T) × U` and a constant `K` with `‖f(s,y) − f(s,z)‖ ≤ K‖y − z‖` whenever
`(s,y), (s,z) ∈ N`. This is the usual ODE meaning next to the separate word "continuous"; it is
weaker than joint local Lipschitz continuity, so the statement is at least as strong as the joint
reading. The norm is the sup norm of `M_d`, which is harmless because `K` is existential and all
norms on `M_d` are equivalent; the derivatives are one-sided at `t = 0` (`HasDerivWithinAt` on `[0, t₀)`);
`T` is real (the case `T = ∞` follows by applying the statement on every `[0, n)`). -/
theorem theorem_4_8 {d : ℕ} (U : Set (Mat d)) (hUsym : ∀ x ∈ U, IsSym x)
    (hUopen : ∃ V : Set (Mat d), IsOpen V ∧ U = V ∩ {x | IsSym x})
    (T : ℝ) (f : ℝ → Mat d → Mat d)
    (hfsym : ∀ t ∈ Set.Ico 0 T, ∀ x ∈ U, IsSym (f t x))
    (hfcont : ContinuousOn (fun q : ℝ × Mat d => f q.1 q.2) (Set.Ico 0 T ×ˢ U))
    (hflip : ∀ q ∈ Set.Ico 0 T ×ˢ U, ∃ N ∈ 𝓝[Set.Ico 0 T ×ˢ U] q, ∃ K : ℝ,
      ∀ s y z, (s, y) ∈ N → (s, z) ∈ N → ‖f s y - f s z‖ ≤ K * ‖y - z‖)
    (hfqm : ∀ t ∈ Set.Ico 0 T, QuasiMonoOn (f t) U)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (x y x' y' : ℝ → Mat d)
    (hxU : ∀ t ∈ Set.Ico 0 t₀, x t ∈ U) (hyU : ∀ t ∈ Set.Ico 0 t₀, y t ∈ U)
    (hx : ∀ t ∈ Set.Ico 0 t₀, HasDerivWithinAt x (x' t) (Set.Ico 0 t₀) t)
    (hy : ∀ t ∈ Set.Ico 0 t₀, HasDerivWithinAt y (y' t) (Set.Ico 0 t₀) t)
    (h0 : PSD (y 0 - x 0))
    (hineq : ∀ t ∈ Set.Ico 0 t₀, PSD ((y' t - f t (y t)) - (x' t - f t (x t)))) :
    ∀ t ∈ Set.Ico 0 t₀, PSD (y t - x t) := by sorry

end AffinePSD.Existence
