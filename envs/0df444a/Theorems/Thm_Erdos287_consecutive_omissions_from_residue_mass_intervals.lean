-- Prove2me | Theorems.Thm_Erdos287_consecutive_omissions_from_residue_mass_intervals
-- name    : Erdos287.consecutive_omissions_from_residue_mass_intervals
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:39:04.013365+00:00
-- url     : https://prove2.me/theorems/d38eba3e-659b-588a-b64c-529cb95ff354
-- title:
--   Residue-specific mass intervals certify consecutive omitted denominators
-- statement:
--   Take a list of distinct scan positions in $[m,M]$ covering the selected denominators $D$, required omissions $H$, and required retained positions $R$. Assume positive denominators in $D$ divide $C$ and $\sum_{n\in D}1/n=1$. Use integer weights $C/n$. The scan keeps a lower and upper possible total in each residue modulo $q$, separately for a retained or omitted leading position. It skips a branch that violates a required position or would omit two consecutive scan entries. If the resulting interval in residue $C\bmod q$ is empty or does not contain $C$, there are two consecutive omissions in $[m,M]$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Combining two-sided mass bounds and the arithmetic test before merging residue states.

import Mathlib

theorem Erdos287.consecutive_omissions_from_residue_mass_intervals (D H R : Finset ℕ) (m M C q : ℕ)
    (hpos : ∀ n ∈ D, 0 < n) (hdiv : ∀ n ∈ D, n ∣ C)
    (hH : Disjoint D H) (hR : R ⊆ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (xs : List ℕ) (hxs : xs.Nodup)
    (hcover : D ⊆ xs.toFinset) (hspan : ∀ n ∈ xs, m ≤ n ∧ n ≤ M)
    (hcert :
      let merge (a b : Option (ℕ × ℕ)) := match a, b with
        | none, b => b
        | a, none => a
        | some a, some b => some (min a.1 b.1, max a.2 b.2)
      let start (g : ZMod q) := if g = 0 then some (0, 0) else none
      let s := xs.foldr
        (fun n (s : Option ℕ × (ZMod q → Option (ℕ × ℕ)) × (ZMod q → Option (ℕ × ℕ))) =>
          (some n,
            fun g => if n ∈ H then none else
              (merge (s.2.1 (g - (C / n : ℕ))) (s.2.2 (g - (C / n : ℕ)))).map
                (fun i => (C / n + i.1, C / n + i.2)),
            fun g => if n ∈ R then none else
              if s.1 = some (n + 1) then s.2.1 g else merge (s.2.1 g) (s.2.2 g)))
        (none, start, start)
      match merge (s.2.1 (C : ZMod q)) (s.2.2 (C : ZMod q)) with
      | none => True
      | some i => C < i.1 ∨ i.2 < C) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by sorry
