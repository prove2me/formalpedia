-- Prove2me | Theorems.Thm_AffineStorage_Ruin_eq_2
-- name    : AffineStorage.Ruin.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:29.958721+00:00
-- url     : https://prove2.me/theorems/3360ed7e-bc3f-47dc-a1b2-f9f41a89e093
-- title:
--   Eq. (2), p. 1284 (PDF 5) — the closed form is the paper's process: flow (2) between jumps, jumps of the right size
-- statement:
--   Let $X$ be the surplus process of the model, started from $X_0=x$, with premium rate $p$ and interest rate $r$.
--
--   1. **Flow between jumps (eq. (2)).** Suppose there are no jump epochs of either stream in $(t_-,t_+)$. Then for every $t\in(t_-,t_+)$,
--   $$X_t=X_{t_-}e^{r(t-t_-)}+\frac pr\big(e^{r(t-t_-)}-1\big).$$
--   2. **Path properties (almost surely).** $X_0=x$. The path $t\mapsto X_t$ is right-continuous, and its left limit at every $t$ is $X_{t-}$. At the epoch of an upward jump of size $U_n$, $X_{T^+_n}-X_{T^+_n-}=U_n$; at the epoch of a claim of size $D_n$, $X_{T^-_n}-X_{T^-_n-}=-D_n$.
--
--   Together these say that the closed-form process of the model definition is the right-continuous process described in §2.1: it grows by (1) between jumps and jumps by the jump sizes. In particular, $X_{t-}$ is the left limit used to define the undershoot.
--
--   **Formalization Note.** Part 1 holds for every sample point. Part 2 holds almost surely, on the event where the epochs are strictly increasing, tend to infinity, and the two streams never share an epoch.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), pp. 1283–1284 (PDF 4–5), §2.1, eq. (2)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem eq_2 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (x : ℝ) :
    (∀ (ω : Ω) (tm tp : ℝ), tm < tp →
        (∀ n, B.Tup n ω ∉ Set.Ioo tm tp ∧ B.Tdown n ω ∉ Set.Ioo tm tp) →
        ∀ t ∈ Set.Ioo tm tp, B.X P x t ω =
          B.X P x tm ω * Real.exp (P.r * (t - tm))
            + P.p / P.r * (Real.exp (P.r * (t - tm)) - 1)) ∧
    (∀ᵐ ω ∂B.P,
      B.X P x 0 ω = x ∧
      (∀ t, ContinuousWithinAt (fun s => B.X P x s ω) (Set.Ici t) t) ∧
      (∀ t, Tendsto (fun s => B.X P x s ω) (𝓝[<] t) (𝓝 (B.Xminus P x t ω))) ∧
      (∀ n, B.X P x (B.Tup n ω) ω - B.Xminus P x (B.Tup n ω) ω = B.Z (2, n) ω) ∧
      (∀ n, B.X P x (B.Tdown n ω) ω - B.Xminus P x (B.Tdown n ω) ω = -B.Z (3, n) ω)) := by sorry

end AffineStorage.Ruin
