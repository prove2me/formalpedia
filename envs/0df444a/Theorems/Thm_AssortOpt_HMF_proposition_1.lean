-- Prove2me | Theorems.Thm_AssortOpt_HMF_proposition_1
-- name    : AssortOpt.HMF.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:21.280277+00:00
-- url     : https://prove2.me/theorems/0e61f2ba-53fd-4baf-af4f-a1c03725051a
-- title:
--   Proposition 1, p. 9 — assortments define IC mechanisms of equal revenue (OPT^S ≤ OPT^x), and every deterministic IC mechanism is an assortment
-- statement:
--   Let $\mathcal L, p$ be a list distribution over items $N = \{1, \dots, n\}$ with prices $r_j \ge 0$.
--
--   1. For every assortment $S \subseteq N$, the mechanism
--   $$x_j(\ell) = \begin{cases} 1, & j \text{ appears before any other item of } S \text{ on } \ell, \\ 0, & \text{otherwise,} \end{cases} \qquad \ell \in \mathcal L,\ j \in \ell \qquad (6)$$
--   is IC and $\mathsf{REV}[x] = \mathsf{REV}[S]$.
--   2. Therefore every assortment's revenue is matched by an IC mechanism: $\mathsf{OPT}^S \le \mathsf{OPT}^x$.
--   3. Conversely, every deterministic IC mechanism (one with $x_j(\ell) \in \{0, 1\}$ for all $\ell \in \mathcal L$, $j \in \ell$) is given by (6) for some assortment $S$.
--
--   This is the ordinal analogue of the fact that in single-buyer auctions a mechanism is deterministic iff it is posted pricing: here deterministic mechanisms are exactly assortments.
--
--   **Formalization Note** "Therefore $\mathsf{OPT}^S \le \mathsf{OPT}^x$" is stated as: for every $S$ there is an IC mechanism with revenue at least $\mathsf{REV}[S]$. The converse compares the mechanisms on the values the LP uses ($\ell \in \mathcal L$, $j \in \ell$).
--
--   Differences from the source:
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - encoding: $\mathsf{OPT}^S \le \mathsf{OPT}^x$ → $\forall S\, \exists x$ IC with $\mathsf{REV}[S] \le \mathsf{REV}[x]$; reason: the optimal values are not named; this is the same inequality.
--   - reading: "deterministic IC mechanism" → IC $x$ with $x_j(\ell) \in \{0,1\}$ for $\ell \in \mathcal L$, $j \in \ell$; reason: the LP's variables are exactly these values.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 9, Proposition 1 (6)

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem proposition_1 {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    (∀ S : Finset (Fin n), IsIC D (assortMech S) ∧ revMech D r (assortMech S) = revAssort D r S) ∧
    (∀ S : Finset (Fin n), ∃ x, IsIC D x ∧ revAssort D r S ≤ revMech D r x) ∧
    (∀ x : List (Fin n) → Fin n → ℝ, IsIC D x →
      (∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, x ℓ j = 0 ∨ x ℓ j = 1) →
      ∃ S : Finset (Fin n), ∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, x ℓ j = assortMech S ℓ j) := by sorry

end AssortOpt.HMF
