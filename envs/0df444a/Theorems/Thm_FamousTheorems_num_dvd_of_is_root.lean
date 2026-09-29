-- Prove2me | Theorems.Thm_FamousTheorems_num_dvd_of_is_root
-- name    : FamousTheorems.num_dvd_of_is_root
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:11.647721+00:00
-- url     : https://prove2.me/theorems/a50c5713-e478-469b-bba9-013be6c220c6
-- title:
--   The rational root theorem
-- statement:
--   **The rational root theorem.** If $p/q$ in lowest terms is a root of an integer polynomial, then $p$ divides the constant coefficient and $q$ divides the leading coefficient. This turns root-finding over $\mathbb{Q}$ into a finite search: only finitely many candidates need testing, so rational roots of an integer polynomial are always computable. It is also the fastest route to irrationality proofs — $\sqrt2$ is a root of $x^2 - 2$, whose only candidate rational roots are $\pm1, \pm2$, none of which work. **Formalization note.** `num` and `den` are the reduced numerator and denominator in the fraction field. The result is Mathlib's `num_dvd_of_is_root`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem num_dvd_of_is_root :
    ∀ {A : Type u_1} {K : Type u_2} [inst : CommRing A] [inst_1 : IsDomain A] 
    [inst_2 : UniqueFactorizationMonoid A] [inst_3 : Field K] [inst_4 : Algebra A K] [inst_5 : IsFractionRing A K] 
    {p : Polynomial A} {r : K}, (Polynomial.aeval r) p = 0 → IsFractionRing.num A r ∣ p.coeff 0 := by sorry

end FamousTheorems
