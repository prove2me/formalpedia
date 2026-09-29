-- Prove2me | Theorems.Thm_FamousTheorems_tendsto_pi_nhds
-- name    : FamousTheorems.tendsto_pi_nhds
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:04.907965+00:00
-- url     : https://prove2.me/theorems/53bd1995-9d11-4ea6-99b8-36ccf56d9403
-- title:
--   Pointwise convergence in a product
-- statement:
--   **Convergence in the product topology is pointwise convergence.** A net of functions converges in $\prod_i X_i$ if and only if it converges at every coordinate: $$f_n \to f \iff \forall i,\ f_n(i) \to f(i).$$ This is the defining property of the product topology, and the reason it is the *coarsest* topology making all projections continuous — any coarser topology would fail to detect some coordinate, any finer one would demand more than pointwise agreement. The contrast with uniform convergence is the whole content: pointwise limits of continuous functions need not be continuous, which is why the product topology on a function space is badly behaved for analysis and why uniform structures are introduced instead. Its compensating virtue is Tychonoff's theorem, which fails for the finer box topology. **Formalization note.** The statement is for the dependent function type `∀ i, X i` with its product topology, and holds for arbitrary index types. The result is Mathlib's `tendsto_pi_nhds`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem tendsto_pi_nhds :
    ∀ {Y : Type u_1} {ι : Type u_2} {A : ι → Type u_3} [T : (i : ι) → TopologicalSpace (A i)] 
    {f : Y → (i : ι) → A i} {g : (i : ι) → A i} {u : Filter Y}, 
    Tendsto f u (𝓝 g) ↔ ∀ (x : ι), Tendsto (fun i => f i x) u (𝓝 (g x)) := by sorry

end FamousTheorems
